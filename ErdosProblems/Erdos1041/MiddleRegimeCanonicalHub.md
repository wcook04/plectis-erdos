# Erdős #1041: the middle regime `2/5 < mu <= 1 - eta`

Status, 2026-09-05 (wave-3 lane D). Four ordinary theorems with exact
certificates, one structural obstruction that retires a whole proof style, a
sharp answer to "what does `mu` force about the root geometry" (the answer is
*almost nothing*, and the little it does force is already sharp), and an
adversarially measured bracket for `eta`. **Erdős #1041 is not proved here, and
no part of `2/5 < mu < 1` is closed in general degree.**

Replay:

```sh
./repo-python formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1041/scripts/check_erdos1041_middle_regime_canonical_hub.py
```

## 0. What this lane was asked, and what came back

The lane was asked to close `2/5 < mu <= 1 - eta` by a canonical hub or an
adjacent chord, with an explicit `eta`. It did not. What it produced instead is
the exact shape of the obstruction, and one scale-free inequality that would
close the lower half of the band outright.

Four things are proved:

- **Theorem A** (§1). On the equality family `(z-tau)^n - lambda` the adjacent
  root chord carries `max |f| = mu (1 + cos^n(pi/n))`, attained *only* at the
  midpoint. So the adjacent chord is contained exactly when
  `mu < kappa_n = 1/(1 + cos^n(pi/n))`, and `kappa_n` decreases strictly from
  `8/9` to `1/2`. In particular `kappa_n > 1/2` at every degree: on the extremal
  family the whole band `2/5 < mu <= 1/2` is covered by the adjacent chord with
  margin, and `1/2` is the exact asymptotic ceiling of that mechanism.
- **Theorem B** (§2). A quantitative centroid-spoke theorem with an explicit
  constant: if the roots are a `delta`-perturbation of a regular `n`-gon about
  their centroid, every centroid spoke satisfies
  `max |f| <= |f(c)| exp(2 delta S_n/(1-delta))` with `S_n` an explicit
  cyclotomic sum. This is the perturbative half of the band, done properly.
- **Theorem C** (§3). The perturbative half is *all* a perturbative argument can
  ever get: `mu` does not control the deviation of the root configuration from a
  regular polygon uniformly in the degree. The family `z(z^{n-1} - r^{n-1})` has
  `mu -> 1` while its eccentricity stays maximal, so `eta` in any theorem proved
  by perturbation of `z^n - lambda` must depend on `n`.
- **Theorem D** (§4). The two-level wall `(z^k - a^k)(z^k + b^k)` is settled in
  closed form across the *entire* band: `mu = a^k b^k`, the origin is
  simultaneously the centroid and the least critical point, and every origin
  spoke has `max |f| = max(a^k b^k, (a^k+b^k)^2/4) < 1`.

The measurement (§5) then does two things. It gives the exact sharpness of what
`mu` forces on the root geometry (§5.1: the Fekete bound `D >= mu^{n-1}` is
attained, `|f(centroid)| < 1` is proved and has no `mu`-margin, the deviation
functional is unbounded). And it brackets `eta` (§5.3): the canonical
disjunction is unrefuted by guarded adversarial climbs down to `eta = 1e-4` at
degree four and `eta = 1e-3` at degree five, and it is **already refuted** at
`eta <= 1.2105e-5` by the quintic of Theorem 4 of
[`HubTaylorSpokeCertificate.md`](HubTaylorSpokeCertificate.md). So the honest
statement of this lane's target is

```text
1.2105e-5 < eta_true <= 1e-4       (bracket; upper end measured, lower end certified)
```

and the middle-regime canonical-hub statement, if true, is true with a margin
that is *not* uniform and is exhausted in the last `1e-4` of the range.

Finally, §6 states the one inequality that would close `2/5 < mu <= 1/2` in a
line, together with the measured evidence for it at degrees three to sixteen.

## 1. Theorem A: the adjacent-chord law on the equality family

Write `omega = e^{2 pi i/n}` and `phi = pi/n`.

> **Theorem A.** Let `n >= 3`, `tau` complex, `lambda` complex with
> `m = |lambda| > 0`, and `f(z) = (z - tau)^n - lambda`. Let `a_0, a_1` be two
> roots of `f` adjacent in argument about `tau`. Then
>
> ```text
> max_{z in [a_0, a_1]} |f(z)|  =  m (1 + cos^n(pi/n)),
> ```
>
> attained at the midpoint of `[a_0, a_1]` and nowhere else on the chord.

*Proof.* Translation and rotation reduce to `tau = 0`, `lambda = r^n > 0`,
`a_j = r omega^j`. On the chord put `z(t) = r u(t)`, `u(t) = (1-t) + t omega`,
`t in [0,1]`, so `|f(z(t))| = m |u(t)^n - 1|`. Since
`(1 + omega)/2 = cos(phi) e^{i phi}` and `omega - 1 = 2 i sin(phi) e^{i phi}`,
with `s = t - 1/2`,

```text
u(t) = e^{i phi} ( cos phi + 2 i s sin phi ) ,
```

and `n phi = pi`, so `u(t)^n = - (A + i B s)^n` with `A = cos phi`,
`B = 2 sin phi`. Hence

```text
|f(z(t))| = m | (A + i B s)^n + 1 | ,        s in [-1/2, 1/2].          (1.1)
```

Write `w = A + i B s`. For `s in [0, 1/2]` set `psi = arg w = arctan(2 s tan phi)`,
so `psi` increases from `0` to `phi` as `s` goes from `0` to `1/2`, and
`|w| = A/cos psi`. Put `X = |w|^n = (cos phi / cos psi)^n`, which increases from
`A^n` to `1`. Then

```text
G(psi) = |w^n + 1|^2 = X^2 + 2 X cos(n psi) + 1 .
```

Since `X' = n X tan psi`,

```text
G'(psi) = 2 n X [ tan psi ( X + cos n psi ) - sin n psi ] .
```

Because `psi <= phi` gives `X <= 1` and `tan psi > 0`,

```text
tan psi (X + cos n psi) - sin n psi
      <= tan psi (1 + cos n psi) - sin n psi
       = 2 tan psi cos^2(n psi/2) - 2 sin(n psi/2) cos(n psi/2)
       = 2 cos^2(n psi/2) [ tan psi - tan(n psi/2) ] ,
```

using `1 + cos x = 2 cos^2(x/2)` and `sin x = 2 sin(x/2) cos(x/2)`. On
`psi in (0, phi)` we have `n psi/2 in (0, pi/2)`, so `cos(n psi/2) > 0`, and
`n psi/2 >= psi` for `n >= 2` with strict inequality for `n >= 3`, so
`tan(n psi/2) > tan psi`. Hence `G' < 0` on `(0, phi)`: `G` is strictly
decreasing, its maximum on `s in [0,1/2]` is at `s = 0`, and `G(0) = (1 + A^n)^2`.
The map `s -> -s` is the reflection symmetry of the chord, so the same holds on
`[-1/2, 0]`. At the other end, `psi = phi` gives `X = 1` and
`cos(n phi) = cos(pi) = -1`, so `G(phi) = 1 - 2 + 1 = 0`, consistent with the
endpoints of the chord being roots of `f`. ∎

> **Corollary A1.** For `f = (z - tau)^n - lambda` with all roots in the open
> unit disc, `mu(f) = m` and the adjacent root chord lies in `{|f| < 1}` if and
> only if
>
> ```text
> mu  <  kappa_n := 1 / (1 + cos^n(pi/n)) .
> ```
>
> `kappa_n` is strictly decreasing in `n` with `kappa_n -> 1/2`, so
> `kappa_n > 1/2` for every `n >= 3`, with exact values
> `kappa_3 = 8/9`, `kappa_4 = 4/5`, `kappa_6 = 64/91`.

*Proof of the monotonicity.* `cos^n(pi/n) = exp(g(n))` with
`g(n) = n log cos(pi/n)`; writing `x = pi/n`,
`g'(n) = log cos x + x tan x =: h(x)` has `h(0) = 0` and
`h'(x) = x sec^2 x > 0`, so `h > 0` on `(0, pi/3]` and `g` is increasing.
Also `g(n) -> 0`, so `cos^n(pi/n) -> 1` and `kappa_n -> 1/2`. Exact values:
`cos(pi/3) = 1/2`, `cos^4(pi/4) = 1/4`, `cos^6(pi/6) = 27/64`. ∎

> **Corollary A2.** On the equality family the adjacent chord covers the whole
> band `2/5 < mu <= 1/2` at every degree, with `max |f| = mu(1 + cos^n(pi/n))
> < 2 mu <= 1`. The constant `2` is asymptotically exact: no bound of the form
> `max |f| <= c · mu` with `c < 2` holds on the family uniformly in `n`.

**Attribution.** The *value* `1 + cos^n(pi/n)` at the regular `n`-gon is already
corpus property: it is the chord objective recorded in negative result 57 of the
kill-list and in the concyclic open item (the reason a Fekete-deficit split must
not use the plain chord), and `concyclic_alternation_theorem` owns the concyclic
statement. Lemma 6 of
[`CentroidVarianceChordChart.md`](CentroidVarianceChordChart.md) proves the
`n = 3` case with the midpoint claim (`9/8 r^3`). What is new here is the
all-degree closed form *with* the location of the maximum, the reduction `(1.1)`
that makes it a one-variable monotonicity statement, and the `mu`-threshold
reading `kappa_n > 1/2` with its exact rational anchors.

**Certificate.** The reduction `(1.1)` is audited at 60 digits for
`3 <= n <= 24`. At `n = 3, 4, 6` — the degrees at which `A^2` and `A^n` are
rational (`1/4, 1/2, 3/4` and `1/8, 1/4, 27/64`) — the polynomial
`G_n(s) = (A^2 + B^2 s^2)^n + 2 Re((A + iBs)^n) + 1` has rational coefficients
and `(1 + A^n)^2 - G_n(s) >= 0` on `[0, 1/2]` is certified by exact Bernstein
positivity, together with `G_n(0) = (1+A^n)^2` and `G_n(1/2) = 0`.

## 2. Theorem B: the quantitative centroid spoke

The instrument is the spoke identity: for any hub `h`, any root `a`, and
`zeta = a - h`,

```text
f(h + s zeta) / f(h) = (1 - s) prod_{i != a} ( 1 - s zeta/(a_i - h) ) .     (2.1)
```

On the equality family with `h = tau` the product is exactly
`prod_{k=1}^{n-1}(1 - s omega^k) = (1 - s^n)/(1 - s)`, so
`f(tau + s zeta) = lambda (s^n - 1)` and every spoke has `max |f| = m` at the
hub end, with margin `1 - m` — the `n`-fold phase cancellation is the entire
content. Theorem B controls its perturbation.

For `k = 1, ..., n-1` put

```text
m_k = min_{s in [0,1]} |1 - s omega^k|
    = |sin(2 pi k/n)|   if cos(2 pi k/n) > 0,   and   1   otherwise,
S_n = sum_{k=1}^{n-1} 1/m_k .
```

`S_n = 2, 3, 4.10292, 5.30940, 6.55810, 7.82843, 10.50553, 13.30940, 19.21946,
25.44980` at `n = 3,4,5,6,7,8,10,12,16,20`.

> **Theorem B.** Let `n >= 3` and let `f` be monic of degree `n` whose roots can
> be written
>
> ```text
> a_j = c + lambda omega^j (1 + delta_j),   j = 0, ..., n-1,
> ```
>
> with `c` the centroid of the roots, `lambda > 0` and `|delta_j| <= delta < 1`.
> Put `E = exp( 2 delta S_n / (1 - delta) ) - 1`. Then for every `j` and every
> `s in [0,1]`,
>
> ```text
> | f( c + s (a_j - c) ) |  <=  |f(c)| (1 + E) .
> ```
>
> Consequently, if `|f(c)| (1 + E) < 1` and `max_j |a_j - c| < 1`, then every
> straight spoke from the centroid to a root lies in `{|f| < 1}`, any two of them
> form a broken line of length `< 2`, and Erdős #1041 holds for `f`.

*Proof.* Fix `j` and put `zeta = a_j - c`. For `i != j`,

```text
zeta/(a_i - c) = omega^{j-i} (1 + delta_j)/(1 + delta_i) = omega^{j-i} (1 + eta_i),
eta_i = (delta_j - delta_i)/(1 + delta_i),   |eta_i| <= 2 delta/(1 - delta).
```

As `i` runs over the indices `!= j`, `k = j - i mod n` runs over `1, ..., n-1`.
By `(2.1)`,

```text
f(c + s zeta)/f(c) = (1-s) prod_{k=1}^{n-1} (1 - s omega^k) ·
                     prod_{k=1}^{n-1} ( 1 - s omega^k eta_{(k)} / (1 - s omega^k) )
                   = (1 - s^n) prod_{k=1}^{n-1} ( 1 - s omega^k eta_{(k)}/(1 - s omega^k) ).
```

Each factor has modulus at most `1 + |eta|/m_k`, and
`prod (1 + x_k) <= exp(sum x_k)`, so the second product has modulus at most
`exp(2 delta S_n/(1-delta)) = 1 + E`, while `0 <= 1 - s^n <= 1`. ∎

Three remarks, all of which matter for how far this can be pushed.

1. The hypothesis is stated at the **centroid**, which makes the hub canonical
   and forces `sum_j omega^j delta_j = 0`; that constraint is not used.
2. `E` is useful only for `delta = O(1/S_n)`, and `S_n` grows superlinearly
   (roughly `(n/pi) log n` plus a linear term; `S_20 = 25.4498`), so the
   admissible perturbation shrinks with the degree.
   That is not an artefact of the estimate: §3 shows no perturbative theorem can
   avoid an `n`-dependent hypothesis.
3. The criterion is expressed in `|f(c)|`, not in `mu`. By Proposition 1 of
   [`CentroidVarianceChordChart.md`](CentroidVarianceChordChart.md),
   `|f(c)| <= Var^{n/2} < 1` always, so the criterion is never vacuous; but §5.1
   shows `mu` does not bound `|f(c)|` away from `1`, so it cannot be converted
   into a `mu`-threshold.

**Certificate.** The cyclotomic identity is audited at 60 digits for
`3 <= n <= 24`; `S_n` is computed with a certified rational upper bound; the
envelope is audited on a fixed-seed float sample: no violation in 1479
admissible draws, and the worst ratio of the true spoke maximum to the bound is
`0.999694`, attained in the small-`delta` limit where `E -> 0`, the bound
degenerates to `|f(c)|`, and the spoke maximum is attained at the hub. The
audit therefore tests the inequality at its equality case as well as away from
it.

## 3. Theorem C: `mu` does not control the root geometry uniformly in `n`

Define the **eccentricity** of a root multiset, an affine invariant that
vanishes exactly on the configurations `(z - tau)^n - lambda`:

```text
ecc(f) = 1 - min_j |a_j - c| / max_j |a_j - c|  in [0, 1),   c = centroid.
```

> **Theorem C.** For `n >= 3` and `0 < r < 1` let
> `f_{n,r}(z) = z (z^{n-1} - r^{n-1})`. Then all roots lie in the open unit
> disc, the centroid is `0`, and
>
> ```text
> mu(f_{n,r}) = (n-1) n^{-n/(n-1)} r^n ,        ecc(f_{n,r}) = 1 .
> ```
>
> All `n-1` critical values have the same modulus `mu`. The centroid is itself a
> root of `f`, and every straight spoke from it to an outer root satisfies
> `max |f| = mu` exactly, so two such spokes give a contained broken line of
> total length `2r < 2`.
> Since `(n-1) n^{-n/(n-1)} -> 1`, for every `m_0 < 1` there is `n_0` such that
> for all `n >= n_0` there are degree-`n` configurations with `mu > m_0` and
> `ecc = 1`.

*Proof.* `f' = n z^{n-1} - r^{n-1}`, so every critical point has
`|c_*| = r n^{-1/(n-1)}` and
`f(c_*) = c_*(c_*^{n-1} - r^{n-1}) = -c_* r^{n-1}(n-1)/n`, giving
`|f(c_*)| = (n-1) r^n n^{-n/(n-1)}` for all `n-1` critical points; hence `mu` is
that common value. The `z^{n-1}` coefficient of `f` is `0`, so the centroid is
`0`, which is a root, so `min_j |a_j - c| = 0` and `ecc = 1`. Along the spoke to
an outer root `a = r zeta`, `zeta^{n-1} = 1`,

```text
f(s a) = s a ( s^{n-1} a^{n-1} - r^{n-1} ) = - s r zeta r^{n-1} (1 - s^{n-1}),
|f(s a)| = r^n s (1 - s^{n-1}) ,
```

whose maximum over `s in [0,1]` is at `s = n^{-1/(n-1)}` with value
`r^n (n-1) n^{-n/(n-1)} = mu`. Finally
`log((n-1) n^{-n/(n-1)}) = log(1 - 1/n) - (log n)/(n-1) -> 0`. ∎

Thresholds crossed (exact, `r -> 1`): `mu > 2/5` first at `n = 4`
(`3 · 4^{-4/3} = 0.472...`), `mu > 1/2` at `n = 5` (`4 · 5^{-5/4} = 0.534...`),
`mu > 3/5` at `n = 7`, `mu > 0.8` at `n = 20`, `mu > 0.9` at `n = 49`.

**Consequences.**

- The near-Fekete rigidity that makes Theorem B work — `mu -> 1` forces the
  configuration towards `(z - tau)^n - lambda` — is a **fixed-degree** statement.
  Its modulus of continuity degenerates as `n` grows, and Theorem C exhibits the
  degeneration explicitly. Any theorem of the shape
  "`2/5 < mu <= 1 - eta` implies a canonical certificate", proved by perturbing
  the equality family, must have `eta = eta(n)` and cannot be uniform.
- The hub set must contain the centroid (equivalently: must be allowed to be a
  root). On this family every critical point is at distance
  `r n^{-1/(n-1)} -> r` from the centroid and the origin/centroid is the unique
  hub whose spokes are all contained. This confirms §8(ii) of the wave brief and
  upgrades it from a sampled observation to a closed form.
- The whole band contains configurations of maximal eccentricity. Any argument
  that begins "in the surviving regime the roots are nearly a regular `n`-gon"
  is false as stated, at every `mu` below `1`, once the degree is large enough.

**Attribution.** The degree-five case of this is already on file as a
measurement: §"Degree five was measured" of
[`FixedDegreeClusterSeparationClosure.md`](FixedDegreeClusterSeparationClosure.md)
records 57921 survivors with `mu > 139/250` of which those below `mu ~ 0.95` sit
up to `1.2166` radians from the regular pentagon, and concludes that
"`mu > mu_5` forces the root polygon within a quantified distance of the regular
pentagon" is false as stated. Theorem C upgrades that from a fixed-degree
measurement to an exact all-degree family, adds the closed form for `mu`, and
supplies the limit `mu -> 1` that makes the failure *uniform*: at each fixed
degree, `mu -> 1` still forces `D -> 1` and hence near-regularity through Fekete
stability, but the `mu` at which the forcing begins tends to `1` with `n`.

## 4. Theorem D: the two-level wall, in closed form across the band

> **Theorem D.** Let `k >= 2` and `0 < b <= a < 1`, and
> `f(z) = (z^k - a^k)(z^k + b^k)`, monic of degree `n = 2k`, all roots in the
> open unit disc. Then the centroid is `0`, the origin is a critical point and
> carries the least critical value,
>
> ```text
> mu(f) = |f(0)| = a^k b^k ,
> ```
>
> the other `k` critical values have modulus `(a^k + b^k)^2/4 >= mu`, and every
> straight spoke from `0` to a root satisfies
>
> ```text
> max |f| = a^k b^k = mu     on the k spokes to the roots of modulus b,
> max |f| = (a^k + b^k)^2/4  on the k spokes to the roots of modulus a,
> ```
>
> both `< 1`. Taking the two inner spokes gives a contained broken line of
> length `2b < 2` whose maximum modulus is exactly `mu`.

*Proof.* `f = z^{2k} + (b^k - a^k) z^k - a^k b^k` has zero coefficient in
`z^{2k-1}` for `k >= 2`, so the centroid is `0`.
`f' = k z^{k-1}(2 z^k + b^k - a^k)`, so the critical points are `0` (multiplicity
`k-1`) and the `k` solutions of `z^k = (a^k - b^k)/2`, at which
`f = ((a^k-b^k)/2 - a^k)((a^k-b^k)/2 + b^k) = -(a^k + b^k)^2/4`. AM–GM gives
`(a^k+b^k)^2/4 >= a^k b^k = |f(0)|`, so `mu = a^k b^k` at the hub `0`. Along the
spoke to a root `alpha` with `alpha^k = a^k`, writing `u = s^k in [0,1]`,
`|f(s alpha)| = a^k (1-u)(u a^k + b^k)`, a downward parabola in `u` with
maximum at `u_* = (a^k - b^k)/(2 a^k) in [0, 1/2]` and value
`a^k (a^k+b^k)^2/(4 a^k) = (a^k+b^k)^2/4`. Along the spoke to a root `beta` with
`beta^k = -b^k`, `|f(s beta)| = b^k (1-u)(u b^k + a^k)`, whose derivative at
`u = 0` is `b^k(b^k - a^k) <= 0`, so the maximum is at `u = 0` and equals
`a^k b^k`. Both values are `< 1` because `a^k + b^k < 2`. ∎

Taking `a = b` gives `mu = a^{2k}`, which sweeps `(0,1)`, so Theorem D settles
the whole band on this family. This is the family the wave brief calls the
"two-level wall" (`(z^3-a^3)(z^3+b^3)`, `mu = 0.707`); the brief's observation
that its origin spokes are contained "with max 0.722" is the case
`k = 3, a = b`, and the closed form above replaces the measurement.

## 5. Measurement

Floating point; falsification evidence only. Instruments: every segment maximum
is the maximum of `|f|^2` restricted to the segment, taken at the exact real
roots of its derivative (a real polynomial of degree `2n-1`), so no path
tracking, no inverse branches, and the saddle-connection wall defect class does
not apply. Guards: no colliding roots (gap `>= 1e-6`), no colliding critical
points (gap `>= 1e-7`), all roots strictly inside the disc. Climbs are
hard-constrained (infeasible proposals rejected outright, no penalty smearing)
with multi-family seeding (uniform disc, near-regular shell `1e-7..1e-1`,
common-modulus shell, central-root).

### 5.1 What `mu` forces about the root geometry (task 1)

Let `D = prod_{i<j}|a_i - a_j|^2 / n^n` be the Fekete ratio, `Var` the second
central moment, `c` the centroid, and `ecc` as in §3. Adversarial
extremisation subject to `mu >= m_0`, degrees 4 to 12:

| functional | what `mu >= m_0` forces | status |
|---|---|---|
| `D` | `D >= m_0^{n-1}`, **and this is attained**, by `z^n - m_0` | proved, sharp |
| `Var` | `Var >= m_0^{2/n}` fails for `n >= 6` | refuted (corpus Thm 5, `z^n - z`) |
| `|f(c)|` | `|f(c)| <= Var^{n/2} < 1`, and `sup |f(c)| = 1` at every `m_0 < 1` | proved; no `mu`-margin |
| `ecc` | nothing uniform in `n`: `ecc = 1` is attainable at every `m_0 < 1` | refuted (Theorem C) |

One cell already shows the `Var` refutation directly: at `n = 8, m_0 = 0.6` the
climb finds `Var = 0.8679` below `m_0^{2/n} = 0.8735`, which cannot happen for
`n <= 5`. Everywhere else the `Var` column sits just above the regular-family
value, which is the corpus's near-equality.

The `D` row is the answer to the question the lane was set. The two-sided
constraint `mu^{n-1} <= D <= 1` cannot be improved on either side: the lower
bound is an equality on the whole equality family (all `n-1` critical values
equal `mu` there, and `prod_j |f(c_j)| = D`), and the upper bound is Fekete.
The climb reproduces `min D = m_0^{n-1}` to three digits at `n = 4, 5` and
converges more slowly above.

Measured extrema (climb; the `D` and `Var` columns are upper bounds for the true
minima, `ecc`-proxy `dev` is a lower bound for the true maximum):

| n | `m_0` | max deviation-from-regular | min `D` (vs `m_0^{n-1}`) | min `Var` (vs `m_0^{2/n}`) | max `|f(c)|/mu` (vs `1/m_0`) |
|---|---|---|---|---|---|
| 4 | 0.4 | 0.6857 | 0.06422 (0.0640) | 0.6388 (0.6325) | 2.4545 (2.5) |
| 4 | 0.5 | 0.4772 | 0.12622 (0.1250) | 0.7084 (0.7071) | 1.9947 (2.0) |
| 4 | 0.6 | 0.4118 | 0.22016 (0.2160) | 0.7749 (0.7746) | 1.6423 (1.667) |
| 4 | 0.8 | 0.2853 | 0.51369 (0.5120) | 0.8958 (0.8944) | 1.2421 (1.25) |
| 5 | 0.4 | 0.7608 | 0.02580 (0.0256) | 0.7013 (0.6931) | 2.4635 (2.5) |
| 5 | 0.5 | 0.7597 | 0.06331 (0.0625) | 0.7723 (0.7579) | 1.9779 (2.0) |
| 6 | 0.4 | 0.7978 | 0.01171 (0.0102) | 0.7419 (0.7368) | 2.4922 (2.5) |
| 6 | 0.5 | 0.8019 | 0.03262 (0.0313) | 0.8050 (0.7937) | 1.9793 (2.0) |
| 8 | 0.4 | 0.8546 | 0.00245 (0.0016) | 0.7992 (0.7953) | 2.4817 (2.5) |
| 8 | 0.5 | 0.8560 | 0.01179 (0.0078) | 0.8625 (0.8409) | 1.9963 (2.0) |
| 8 | 0.6 | 0.8548 | 0.02839 (0.0168) | 0.8679 (0.8735) | 1.6610 (1.667) |
| 8 | 0.8 | 0.2060 | 0.32236 (0.2097) | 0.9459 (0.9457) | 1.2448 (1.25) |
| 10 | 0.4 | 0.8875 | 0.00041 (0.00026) | 0.8347 (0.8326) | 2.4669 (2.5) |

The deviation column is the point. It grows with the degree at fixed `m_0`, and
at `m_0 = 0.4, 0.5` it is already tracking the central-root family of Theorem C
(`dev = 0.5773, 0.7515, 0.8854, 0.9794` at `n = 3, 5, 10, 50`), whose true value
is `ecc = 1`. The drop at `m_0 = 0.6` for `n <= 6`, and at `m_0 = 0.8` for `n <= 8`, is
exactly the constraint that `f_{n,r}` cannot reach those `mu` below `n = 7`
and `n = 20`: at `n = 8, m_0 = 0.6` the deviation is back up at `0.8548`
because `f_{8,r}` reaches `mu = 0.6273 > 0.6`, and at `n = 8, m_0 = 0.8` it
collapses to `0.2060` because it does not reach `0.8`.  The measured deviation
ceiling is the central-root family, degree by degree.

**Reading.** Nothing in the surviving regime is a near-Fekete regime except by
degree-dependent accident. The corpus's `HardRegimeIsNearFekete.md` describes
where the *hub obstruction* lives (`D > 0.99994`); it does not describe where
the regime `2/5 < mu < 1` lives.

### 5.2 The chord-to-critical ratio

Define the affine-invariant, scale-free quantity

```text
Q(f) = ( min_{i<j} max_{[a_i,a_j]} |f| ) / mu(f) .
```

`Q < 1/mu` is exactly "some root chord is contained". Adversarial maximisation
of `Q` subject to `mu >= 2/5`, 8 to 14 restarts per degree:

| n | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 12 | 14 | 16 |
|---|---|---|---|---|---|---|---|---|---|---|---|
| `sup Q` found | **1.125000** | 1.156279 | 1.206108 | 1.238942 | 1.269235 | 1.305422 | 1.304635 | 1.348611 | 1.325591 | 1.351883 | 1.365675 |
| `1 + cos^n(pi/n)` | 1.125000 | 1.25 | 1.346568 | 1.421875 | 1.481913 | 1.530790 | 1.571311 | 1.605429 | 1.659668 | 1.700834 | 1.733133 |
| ratio | 1.000 | 0.925 | 0.896 | 0.871 | 0.856 | 0.853 | 0.830 | 0.840 | 0.799 | 0.795 | 0.788 |

The `n = 12` to `n = 16` rows come from a separate climb that also seeds multi-cluster
configurations (`k` tight clusters at independent centres, cluster scale
`1e-3` to `1e-1`), the family most likely to break a chord bound, and they do
not move `sup Q` above `1.37`.

At `n = 3` the maximiser is the regular triangle to seven digits
(deviation `0.0`) and `sup Q = 9/8` is Theorem A. At every measured degree the
climb stays strictly below the Theorem A constant, and the ratio falls slowly
with the degree. Removing the `mu`
constraint does not change the picture (`n = 5`: `1.2147`, found at
`mu = 0.0217`), so `Q` is not a large-`mu` phenomenon.

The complementary climb — maximise the best-chord maximum `J` subject to
`mu <= m_0` — gives, at degrees 3 to 6:

| n \ `m_0` | 0.4 | 0.5 | 0.6 | 0.8 | 0.9 |
|---|---|---|---|---|---|
| 3 | 0.4498 | 0.5622 | 0.6745 | 0.8998 | **1.0121** |
| 4 | 0.4597 | 0.5610 | 0.6885 | 0.9226 | **1.0288** |
| 5 | 0.4712 | 0.6002 | 0.7166 | 0.9516 | **1.0398** |
| 6 | 0.4873 | 0.6161 | 0.7380 | 0.9872 | — |

Chordless configurations first appear between `m_0 = 0.8` and `m_0 = 0.9` at
every degree reached. At `n = 3` the climb reproduces `0.4 · 9/8 = 0.45` and
`0.9 · 9/8 = 1.0125` to four digits, so the measured chordless floor is
`mu = 8/9`; Theorem A shows `8/9` is attained (the regular triangle at
`mu = 8/9` is exactly on the boundary), and Lemma 6 of the chord chart shows
independently that the regular triangle minimises `Var` among chordless cubics,
but that the floor is *exactly* `8/9` is a measurement, equivalent to
`sup Q_3 = 9/8`, not a theorem.

### 5.3 The canonical disjunction, and the bracket for `eta`

Let `H = {0, centroid, c_*} ∪ {critical c : |f(c)| < 1}` and

```text
V(f) = min( min_{i<j} max_{[a_i,a_j]} |f| ,
            min_{h in H} min over root pairs of max( spoke max at a, spoke max at b )
                          subject to |a-h| + |b-h| < 2 ) .
```

`V < 1` is exactly "the canonical disjunction certifies `f`". Adversarial
maximisation of `V` subject to `mu <= 1 - eta`:

| n | `eta = 1e-1` | `1e-2` | `1e-3` | `1e-4` |
|---|---|---|---|---|
| 4 | 0.8999866 | 0.9900035 | 0.9990036 | 0.9999000 |
| 5 | 0.8999867 | 0.9900360 | 0.9988496 | — |

In every cell `sup V` lands on `1 - eta` to within `4e-5`, and the winning
configuration has `V` equal to `mu` to within the same tolerance: the
disjunction value is **pinned at `mu` from above**, exactly as §4.1 of
[`HubTaylorSpokeCertificate.md`](HubTaylorSpokeCertificate.md) reports for the
`(A*)` criterion. No failure was found at any `eta >= 1e-4`.

Independently, the checker's fixed-seed census of 1195 random survivors with
`mu > 2/5` at degrees 4 to 8 (uniform-disc, near-regular-shell and central-root
families) records worst disjunction values `0.999997826, 0.999999792,
0.999998099, 0.999999725, 0.999992125` — every one strictly below `1`, and every
one within `1e-5` of it, because the near-Fekete-seeded survivors have
`mu -> 1` and `V` tracks `mu`. The worst chord-to-`mu` ratios in the same census
are `1.118, 1.189, 1.187, 1.242, 1.168`.

That is a basin statement, and it must be read against the certified failure on
the other side. Theorem 4 of `HubTaylorSpokeCertificate.md` exhibits an exact
quintic (roots stored as IEEE-754 hex literals) at which **no** hub of `H`
carries two contained straight spokes.

That note certifies `mu >= 0.9999871398`, which is the wrong direction for
capping `eta`: the statement "`mu <= 1 - eta`" needs an *upper* bound on `mu`.
This lane supplies one, exactly, from the same note's Rouché data. Each disc
`D(centre_i, 2^-30)` holds exactly one critical point and `|f'| <= 5 · 3^4` on
`|z| <= 2`, so

```text
mu  <=  min_i |f(centre_i)| + 405/2^30  =  0.99998789419549...,
1 - mu  >=  1.2105804507e-05 ,
```

all in exact `Fraction` arithmetic (the constant is a stored exact rational in
the checker). An independent evaluation of the witness with this lane's segment
instrument agrees: `mu = 0.9999875170098498`, the best hub value is
`1.0000025938624` (attained at the origin, with the centroid at
`1.0000025955742` and the three admissible critical hubs at `1.0000026877`,
`1.0000041002` and `1.0000254740`), and the best of the ten root chords is
`1.0114012742`. So

```text
the middle-regime canonical-hub statement is FALSE for every eta <= 1.2105e-5,
and unrefuted by adversarial climbs for eta >= 1e-4.
```

Evidence classes differ across that sentence and must not be merged. The hub
half of the refutation is exact (Theorem 4's Bernstein/Rouché certificate); the
chord half is floating point, here and in the source note; the `eta` cap
`1.2105e-5` is exact; and the `1e-4` end is a basin statement.

The lane's target `eta` therefore lies in `(1.2105e-5, 1e-4]` if it exists at all,
and the "middle regime" is genuinely the whole band minus a shell of thickness
at most `1e-4`. Two further exact data points inside the band, both audited here
with the segment instrument:

- the minimal-degree MEC counterexample (negative result 46: roots
  `L(7 ± 24i)/25, -L`, `L = 999/1000`) has `mu = 0.94309573`, all three chords
  failing (`1.00915`) and the origin failing (`1.00679`), while the **centroid**
  hub succeeds (`0.96553`) and each critical hub succeeds with value exactly
  `mu`. The chord and origin disjuncts are individually dead well inside the
  band; the union is not.
- Theorem D and Theorem C supply exact hub certificates at every `mu` in the
  band, on two families that are as far from the equality family as the
  invariants of §5.1 allow.

### 5.4 Which `(n, mu)` cells remain

Closed unconditionally by the corpus: `n = 3` entirely
(`cubic_minimal_critical_value_short_hub`); `mu <= 2/5` at every degree
([`HyperbolicPackingArityFloor.md`](HyperbolicPackingArityFloor.md)); and the
fixed-degree constants of
[`FixedDegreeClusterSeparationClosure.md`](FixedDegreeClusterSeparationClosure.md).
Combining, the open cells are exactly:

| n | closed up to | open cell |
|---|---|---|
| 3 | — | none (fully proved) |
| 4 | `61/100 = 0.610204` | `(0.6102, 1)` |
| 5 | `139/250 = 0.556564` | `(0.5566, 1)` |
| 6 | `253/500 = 0.506687` | `(0.5067, 1)` |
| 7 | `23/50 = 0.460759` | `(0.4608, 1)` |
| 8 | `209/500 = 0.418688` | `(0.4187, 1)` |
| `>= 9` | `2/5` | `(0.4, 1)` |

**This lane closes no new cell.** Theorems A, B, C, D are family statements, an
explicit perturbative criterion, and an obstruction; none of them is a
`mu`-threshold in general degree. What the lane contributes to the cell table is
the knowledge that the cells cannot be attacked perturbatively (Theorem C), that
they cannot be attacked through `D`, `Var`, `|f(c)|` or any deviation functional
conditioned on `mu` (§5.1), and that the canonical disjunction survives in them
down to a shell of thickness at most `1e-4` (§5.3).

Conjecture Q of §6 would close `mu <= 1/2` at every degree. Against the table
above that is new only for `n >= 7`, where it would add the cells
`(0.4608, 0.5]`, `(0.4187, 0.5]` and `(0.4, 0.5]`; at `n = 4, 5, 6` the
fixed-degree constants already exceed `1/2`.

## 6. The smallest open sub-statement

> **Conjecture Q.** For every monic `f` of degree `n >= 3` with distinct roots,
>
> ```text
> min_{i<j}  max_{z in [a_i, a_j]} |f(z)|   <=   ( 1 + cos^n(pi/n) ) · mu(f)
>                                           <    2 mu(f) .
> ```

Both sides are affine-covariant of the same weight, so the statement is
invariant under `z -> alpha z + beta` and the unit disc plays no role in it. It
is an equality at `n = 3` on the regular triangle (Theorem A), and §5.2 measures
it at degrees 3 to 16 with the worst observed ratio `sup Q / (1 + cos^n(pi/n))`
equal to `1.00` at `n = 3` and `0.79` to `0.93` afterwards.

> **Corollary (would close the lower half of the band).** Conjecture Q implies:
> every monic `f` with all roots in the open unit disc and `mu(f) <= 1/2` has a
> root chord contained in `{|f| < 1}`, of length `< 2`. Combined with
> `LowCriticalPotentialClosure.md` / `HyperbolicPackingArityFloor.md` this would
> close `mu <= 1/2` unconditionally at every degree, leaving `1/2 < mu < 1`.
> Against the cell table of §5.4 the new content is at `n >= 7`.

The weak form `min chord <= 2 mu` is what is actually needed; the sharp constant
is stated because the equality family says it is the truth. Two structural
facts recommend the conjecture as the next target. First, it is a statement
about *distances and one critical value*, with no hub, no selector, and no path
tracking — the entire selector-counterexample family of this directory
(negative results 8, 17, 20, 46, 54) attacks *selectors*, and a `min` over pairs
has none. Second, the two families that defeat the hub disjunction from opposite
sides both satisfy it with room: on `z(z^{n-1}-r^{n-1})` the chord from the
central root to any outer root has `max |f| = mu` exactly, so `Q = 1`; on the
two-level wall the inner-polygon chord is likewise controlled.

The obvious proof route (short-pair localisation: take the closest root pair,
where a critical point sits near the midpoint and `max |f|` on the chord is
comparable to that critical value) is *not* known to work: there need be no
critical point between the closest pair, and the comparison degrades exactly
when the configuration is spread out. Nothing here proves the conjecture, and
`sup Q` growing from `1.125` to `1.366` between `n = 3` and `n = 16` leaves open
whether it is bounded at all; the honest weaker target is `sup_n sup_f Q(f) < 2`.

## 7. Routes tried here that failed, precisely

- **Absolute-value spoke bounds at the centroid.** Bounding `(2.1)` by
  `prod (1 + s d_a/d_i)` reproduces the functional `Psi` of §3 of
  `HubTaylorSpokeCertificate.md`, whose ceiling is `1/c_4 = 0.219420` at every
  degree. Confirmed dead; do not re-derive it. Every phase-free spoke estimate
  dies at the equality family for the reason given there (`b_i = 0` while
  `e_{n-i}(d)` is maximal).
- **Converting Theorem B into a `mu`-threshold.** Blocked by §5.1: at every
  `m_0 < 1` in the band, `sup |f(c)| = 1`, so `|f(c)|(1+E) < 1` has no
  `mu`-margin. The obstruction is real, not an artefact of `E`.
- **Any near-regular hypothesis inferred from `mu`.** Blocked by Theorem C.
  This kills, uniformly in `n`: near-Fekete cusp expansions applied to the
  middle regime, "in the surviving regime the roots nearly form a regular
  `n`-gon", and any `eta` derived from a fixed-degree rigidity modulus.
- **Second-moment routes into the band.** `Var >= mu^{2/n}` (the natural
  companion to the `D` row of §5.1) is false for `n >= 6` — this is Theorem 5 of
  `CentroidVarianceChordChart.md`, and the present climbs reproduce its
  near-equality at `n = 4, 5` and its failure direction above. The variance
  chord chart therefore cannot be composed with a `mu`-threshold.
- **Improving `D >= mu^{n-1}`.** Impossible: §5.1 shows the bound is an equality
  on the whole equality family. Any deviation functional bounded by `mu`
  through `D` inherits an exponentially weak constant.
- **The regular polygon as the `Q`-maximiser for `n >= 4`.** False: for even `n`
  the diameter chord of `z^n - m` has `max |f| = m`, so `Q = 1` there, and the
  measured maximisers at `n >= 4` have deviation `0.08` to `0.14`. The Theorem A
  constant is a bound in the measurements, not an extremal value.

## 8. Claim boundary

Proved unconditionally: Theorem A with Corollaries A1, A2 (the adjacent-chord
law on the equality family, its exact threshold `kappa_n`, and its monotonicity
and limit); Theorem B (the quantitative centroid-spoke envelope); Theorem C (the
central-root family's `mu`, eccentricity, spoke maximum and limit); Theorem D
(the two-level wall's `mu`, critical spectrum and every origin spoke maximum).
The `D >= mu^{n-1}` sharpness statement of §5.1 is proved (lower bound is corpus
property; the equality case is the equality family).

Certified exactly (rational / integer arithmetic): the `n = 3, 4, 6` Bernstein
certificates for Theorem A, the exact `kappa` anchors `8/9, 4/5, 64/91`, the
exact rational thresholds for Theorem C at `n = 4, 5, 7, 9, 20, 50`, and the
exact rational Theorem D rows spanning `mu` from `0.5184` to `0.99451`, and the
exact `eta` cap `242116090153607795109973/20000000000000000000000000000`.

Measured only, with no universal authority: everything in §5.1's table,
§5.2, §5.3, and the evidence for Conjecture Q. The `eta`-bracket's lower end
`1.2105804507e-05` is exact — it is proved here from the Rouché enclosure and
Lipschitz constant of `HubTaylorSpokeCertificate.md` — but the refutation it
caps is exact only in its hub half; the chord half of that witness is floating
point in the source note and in this one. The bracket's upper end `1e-4` is a
basin statement from finitely many climbs and negative result 19 of the
kill-list applies to it in full.

Not proved: Erdős #1041; any part of `2/5 < mu < 1` in general degree;
Conjecture Q; and the existence of any `eta > 0` for which the middle-regime
canonical-hub statement holds.

## 9. Consumers

- [`HubTaylorSpokeCertificate.md`](HubTaylorSpokeCertificate.md): §5.3 here
  brackets the `eta` its Theorem 4 leaves open, and §5.1 explains why its
  residual `inf N > 0` question cannot be settled by any `mu`-conditioned bound
  on the root geometry.
- [`CentroidVarianceChordChart.md`](CentroidVarianceChordChart.md): Theorem A
  generalises its Lemma 6 to every degree; §5.1 reproduces its Theorem 5
  refutation direction from the extremisation side; §5.2 locates the chordless
  region in the `mu` coordinate rather than the `Var` coordinate.
- [`GeneralSpokeIdentity.md`](GeneralSpokeIdentity.md): Theorem B is the
  perturbative sharpening of criterion (SC) at a canonical (centroid) hub rather
  than a critical hub, and §7 records that the crude absolute form is the same
  dead route as §3 of the hub-Taylor note.
- [`HardRegimeIsNearFekete.md`](HardRegimeIsNearFekete.md): Theorem C shows the
  identification of the hard regime with the near-Fekete shell is a fixed-degree
  statement whose modulus degenerates with `n`.
- [`HyperbolicPackingArityFloor.md`](HyperbolicPackingArityFloor.md) /
  [`FixedDegreeClusterSeparationClosure.md`](FixedDegreeClusterSeparationClosure.md):
  the corollary of Conjecture Q in §6 would meet the `mu <= 2/5` closure at
  `1/2` and leave only `1/2 < mu < 1`.
