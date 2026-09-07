# Erdős #1041: the chord-minimum conjecture

Status, 2026-09-05 (wave-4 lane A). Conjecture Q of
[`MiddleRegimeCanonicalHub.md`](MiddleRegimeCanonicalHub.md) §6 — here called
**Q_chord** — survives an adversarial, wall-free, disc-free falsification
campaign at degrees 3 to 30. It is **not proved**, and neither is its weak form;
**Erdős #1041 remains open and no new `(n, mu)` cell is closed by this note.**

What is new: four ordinary theorems (one of them settles Q_chord outright on a
whole affine-invariant class at every degree), a sharp hub-free *reduction* of
the weak form to a lemniscate-containment statement that is an **equality** on
every family and every sample examined, exact all-degree certificates on three
families including the parent conjecture's equality family, the identification
of the true near-extremal family (geometric progressions / circle-rotation
orbits, not near-regular polygons), a correction to the framing of the sharp
constant, and a measured asymptotic for `sup_f Q`.

Replay:

```sh
./repo-python formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1041/scripts/check_erdos1041_chord_minimum.py
```

## 0. The invariant and the conjecture

For monic `f` of degree `n >= 2` with distinct roots `a_1, ..., a_n`, put

```text
mu(f) = min { |f(c)| : f'(c) = 0 } ,
Q(f)  = ( min_{i<j} max_{z in [a_i,a_j]} |f(z)| ) / mu(f) .
```

Both numerator and denominator are affine covariant of weight `n`
(`z -> alpha z + beta`, `f -> alpha^n f((z-beta)/alpha)` scales both by
`|alpha|^n`), so `Q` is **affine invariant**: the unit disc plays no role, there
is no hub, no selector and no path tracking anywhere in the statement.

> **Conjecture Q_chord (sharp form).** `Q(f) <= 1 + cos^n(pi/n)` for every `n >= 3`.
>
> **Weak form.** `Q(f) <= 2`.

The weak form settles Erdős #1041 for `mu <= 1/2` at every degree: the chord is
a contained segment, and its length is `< 2` because the roots lie in the open
unit disc. Against the landed cell table
([`MiddleRegimeCanonicalHub.md`](MiddleRegimeCanonicalHub.md) §5.4) the new
content would be at `n >= 7`.

Write `S_n = sup { Q(f) : deg f = n, roots distinct }`.

## 1. Lemma 0: `Q >= 1`, always

> **Lemma 0.** For every monic `f` with distinct roots and every root pair,
> `max_{[a_i,a_j]} |f| >= mu(f)`. Hence `Q(f) >= 1`, and `S_n >= 1`.

*Proof.* Fix `t < mu`. Let `U` be a component of `{|f| < t}`. `U` is bounded and
**simply connected**: a bounded component `V` of `C \ U` would have
`|f| = t` on `∂V ⊂ ∂U`, hence `|f| <= t` on `V` by the maximum principle, so
`V ⊂ {|f| < t}` — impossible unless `V ⊂ U`. So `f : U -> D_t` is a proper map
of a simply connected domain onto a disc, of degree `d` = the number of zeros of
`f` in `U`; by Riemann–Hurwitz it has `d - 1` critical points in `U`. There are
none, because `|f(c)| >= mu > t` at every critical point. So `d = 1`: every
component of `{|f| < t}` contains exactly one root. Two distinct roots therefore
lie in different components, and any path between them — the segment in
particular — leaves the first component, so its maximum is `>= t`. Let `t` rise
to `mu`. ∎

Lemma 0 is the **instrument health guard** used throughout §7: any float sample
reporting `Q < 1` is a numerical failure, not data.

## 2. Theorem 1: collinear roots

> **Theorem 1.** If the roots of `f` are distinct and collinear, then
> `Q(f) = 1`. In particular Q_chord holds, in its sharp form and with room, for
> every real-rooted polynomial and every affine image of one, at every degree.

*Proof.* `Q` is affine invariant, so assume the roots real,
`a_1 < a_2 < ... < a_n`, and `f` real. By Rolle each gap `(a_i, a_{i+1})`
contains a zero of `f'`, and there are `n-1` gaps and `n-1` zeros, so each gap
contains exactly one critical point `c_i` and there are no others. On
`[a_i, a_{i+1}]` the real function `f` vanishes at both ends and has one interior
stationary point, so `max_{[a_i,a_{i+1}]} |f| = |f(c_i)|`. Choose `i` with
`|f(c_i)| = mu`. Then the chord minimum is `<= mu`, and `>= mu` by Lemma 0. ∎

This kills the collinear and near-collinear attack families outright, and by
continuity gives `Q <= 1 + o(1)` on any family degenerating to a collinear
configuration.

## 3. Theorem 2: cluster embedding, and what the sequence `S_n` is

> **Theorem 2.** For `2 <= k < n`, `S_n >= S_k`. So `(S_n)_{n>=2}` is
> nondecreasing and `S := lim_n S_n = sup_n S_n` exists in `[1, infinity]`.
> The weak form of Q_chord is exactly the statement `S <= 2`.

*Proof.* Let `g` be monic of degree `k` with distinct roots `b_1,...,b_k`. Put
`R_l = 3 + l` for `l = 0, ..., n-k-1`, `H(z) = prod_l (z - R_l)`, and

```text
f_eps(z) = prod_{i=1}^{k} (z - eps b_i) · H(z)  =  eps^k g(z/eps) H(z) .
```

*Critical points.* In the inner variable `z = eps zeta`,
`f_eps'(eps zeta) = eps^{k-1} [ g'(zeta) H(eps zeta) + eps g(zeta) H'(eps zeta) ]`,
which converges locally uniformly to `H(0) g'(zeta)`, `H(0) = prod(-R_l) != 0`.
By Hurwitz the `k-1` inner critical points satisfy `c_i(eps) = eps(gamma_i + o(1))`
with `gamma_i` the critical points of `g`, and
`|f_eps(c_i)| = eps^k |H(0)| |g(gamma_i)| (1 + o(1))`. Away from the origin
`f_eps -> z^k H(z)` locally uniformly on `C \ {0}`, so the remaining `n-k`
critical points converge to the `n-k` critical points of `z^k H(z)` that are not
at `0`; at each of those `|z^k H| >= c_0 > 0`. Hence for small `eps`,
`mu(f_eps) = eps^k |H(0)| mu(g) (1 + o(1))`.

*Chords.* An inner chord `[eps b_i, eps b_j]` has
`max |f_eps| = eps^k |H(0)| max_{[b_i,b_j]} |g| (1+o(1))`. A chord with an outer
endpoint `R_l` crosses the circle `|z| = 1`, where
`|f_eps| = eps^k |g(z/eps)| |H(z)| -> |z|^k |H(z)| >= min_{|z|=1} |H| > 0`. A
chord between two outer roots lies in `Re z >= 3`, where at its midpoint
`|z|^k |H(z)| >= 3^k · 4^{-1} · 2^{-(n-k-2)} > 0`. So all non-inner chords have
maxima bounded below by a positive constant while inner chords are `O(eps^k)`;
for small `eps` the chord minimum is attained inside the cluster and
`Q(f_eps) -> Q(g)`. ∎

Two consequences used later.

- The multi-scale families (tight clusters, "pulled pairs", cluster-of-clusters)
  contribute **nothing new** at degree `n`: they realise, in the limit, the
  degree-`k` value of their dominant cluster. This is also why the
  floating-point instrument may legitimately refuse them (§7.0): they are the
  configurations whose `|f|` spans hundreds of orders of magnitude, and they are
  already covered by lower degrees.
- The asymptotic question of task 3 is exactly: is `S` equal to `2`, below `2`,
  or infinite?

## 4. Theorem 3: the 2-reduction, and the sharp statement underneath Q_chord

Let `c*` be a **least critical point**, `f(c*) != 0`, `mu = |f(c*)|`, and set

```text
W = f - f(c*) ,          L = { z : |W(z)| <= mu } .
```

> **Theorem 3.**
> 1. `W` is monic of degree `n` with `W(c*) = W'(c*) = 0`, and `|W(a)| = mu` at
>    **every** root `a` of `f`. So every root of `f` lies on `∂L`, and for every
>    root pair `max_{[a,b]} |W| >= mu`, with equality iff `[a,b] ⊂ L`.
> 2. If `[a,b] ⊂ L` then `max_{[a,b]} |f| <= |f(c*)| + max_{[a,b]} |W| <= 2 mu`.
> 3. If `[c*,a] ⊂ L` and `[c*,b] ⊂ L` then the broken line `a -> c* -> b` has
>    `max |f| <= 2 mu`.
> 4. The component `L_0` of `L` containing `c*` carries at least two roots of
>    `f` on its boundary: `W|L_0 : L_0 -> D̄_mu` is proper of degree `d >= 2`
>    (the double zero of `W` at `c*`), `W'` = `f'` is nonzero at every root of
>    `f`, and exactly `d` roots of `f` lie on `∂L_0`.
> 5. (Necessary condition.) If `[c*, a] ⊂ L` then
>    `Re( (a - c*) f'(a) / f(c*) ) <= 0`.

*Proof.* (1) `W(a) = f(a) - f(c*) = -f(c*)` for every root, so `|W(a)| = mu`;
the rest is the definition of `L` and the fact that a segment with both
endpoints on `∂L` has maximum `>= mu`, with equality exactly when it never
leaves. (2) and (3) are the triangle inequality `|f| <= |f(c*)| + |W|`.
(4) `L_0` is simply connected by the argument of Lemma 0 applied to `|W|`, and
`W|L_0` is proper onto `D̄_mu` of degree `d` = number of zeros of `W` in `L_0`,
which is at least the multiplicity `2` at `c*`. Near a root `a` of `f` we have
`W'(a) = f'(a) != 0`, so `W` is a local homeomorphism there and exactly one
preimage branch of the value `-f(c*)` converges to `a`; letting the `d`
preimages of `v` with `|v| < mu` tend to the boundary gives `d` distinct roots
on `∂L_0`. (5) Along `z(t) = c* + t(a - c*)`, `phi(t) = log|W(z(t))|` satisfies
`phi(1) = log mu` and `phi <= log mu` on `[0,1]` if the segment is in `L`; hence
`phi'(1) >= 0`, and `phi'(1) = Re((a-c*) W'(a)/W(a)) = Re((a-c*) f'(a)/(-f(c*)))`. ∎

Theorem 3 converts the weak form into a hub-free, selector-free **containment**
statement with no constant to lose:

> **Conjecture R (chord form).** Some root chord of `f` lies in
> `L = {|f - f(c*)| <= mu}`. Equivalently
> `R(f) := min_{i<j} max_{[a_i,a_j]} |f - f(c*)| / mu = 1`.
>
> **Conjecture S (spoke form).** Two of the segments `[c*, a]` lie in `L`.
> Equivalently `S(f) := (second smallest of max_{[c*,a_i]} |f - f(c*)|)/mu = 1`.

By Theorem 3(1), `R >= 1` and `S >= 1` **always**, so each conjecture asserts an
exact equality, not an inequality with slack. `Conjecture R` implies the weak
form of Q_chord; `Conjecture S` implies the broken-line form (enough for
Erdős #1041 once the length `|a - c*| + |c* - b| < 2` is available, which it is
not in general — see §8).

`R = 1` is **proved exactly** on three all-degree families in §5, and neither
`R > 1` nor `S > 1` has been produced by any adversarial climb or census in this
lane (§7.3), including at the configurations that maximise `Q`.

Theorem 3(5) is a cheap diagnostic: over 2400 configurations at
`n = 3,4,5,6,8,10` from all eleven seed families, the number of roots satisfying
`Re((a-c*) f'(a)/f(c*)) <= 0` was **exactly two** in every single case. So the
spoke certificate has, generically, exactly one candidate pair — the pair on
`∂L_0` — and `Conjecture S` says that candidate always works.

## 5. Exact all-degree families

> **Theorem 4 (four exact rows).**
> (a) *Equality family.* `f = (z-tau)^n - lambda`, `m = |lambda|`. Then `c* = tau`,
> `mu = m`, `W = (z-tau)^n`, all roots lie on `|z - tau| = m^{1/n}`, and every
> root chord lies in the closed disc, so `|W| <= m` on it: **`R = 1`, hence
> `Q <= 2`, on the whole equality family at every degree**. Moreover for **even**
> `n` the diameter chord gives `|f(ta)| = 1 - t^n` (after normalising `m=1`,
> `tau=0`), so `Q = 1` exactly; for `n = 3` every chord is adjacent and
> `Q = 9/8 = 1 + cos^3(pi/3)` exactly.
> (b) *Central-root family.* `f = z(z^{n-1} - r^{n-1})`. The chord from the
> central root to any outer root has its maximum **at a critical point**
> (`1 - n s^{n-1} = 0` is `f'(sr zeta)/r^{n-1} = 0` up to sign), and all `n-1`
> critical values share one modulus, so the chord maximum equals `mu`:
> `Q = 1` exactly, at every degree and every `r`.
> (c) *Two-level wall.* `f = (z^k - a^k)(z^k + b^k)`, `0 < b <= a`. Then `c* = 0`,
> `mu = a^k b^k`, `W = z^k(z^k + b^k - a^k)`, and on the chord between two
> adjacent inner roots `|W| <= x(x + a^k - b^k)` at `x = b^k|u|^k <= b^k`, which
> is increasing in `x >= 0` and equals `mu` at `x = b^k`: `R = 1`, hence
> `Q <= 2`, for every `k` and every `0 < b <= a`.
> (d) *Collinear.* `Q = 1` (Theorem 1).

All four are certified in exact arithmetic by the checker (blocks 1–4): integer
and `Fraction` arithmetic for (a), (c) and the `9/8` reduction, `sympy` for the
identity in (b).

**Framing correction (this matters for how the conjecture is stated).** The
constant `1 + cos^n(pi/n)` is the *adjacent-chord* value on the equality family
(Theorem A of [`MiddleRegimeCanonicalHub.md`](MiddleRegimeCanonicalHub.md)), but
`Q` is a **minimum over all pairs**, and for `n >= 4` the equality family has
much cheaper non-adjacent chords: `Q = 1` exactly for even `n`, and
`Q = 1.0113, 1.0017, 1.0003, 1.00006` at `n = 5, 7, 9, 11`. So

```text
Q( (z-tau)^n - lambda ) = 1 + cos^n(pi/n)   only at n = 3 ;
```

the equality family is **not** the extremal configuration of `Q` at any degree
`>= 4`, and the sharp constant of Q_chord is attained only at the equilateral
triangle. The honest reading of the conjecture is `S_n <= 1 + cos^n(pi/n)` as a
*bound of convenience* whose right-hand side happens to grow at roughly the same
rate as the measured `S_n`; the real question is whether `S = lim S_n < 2`.

## 6. Degree three in closed form

Every cubic with distinct roots is affinely equivalent to exactly one member of

```text
f_m(z) = (z - (m-1)) (z - (m+1)) (z + 2m) ,      m in C ,
```

(centroid `0`, half-difference of two roots normalised to `1`), and
`Q(f_m) = Q(-m) = Q(conj m)`. With `delta = (a_j - a_i)/2` and
`beta = 3 a_k/(2 delta)` for the pair `(i,j)` with third root `a_k`, the chord
parametrisation `z = -a_k/2 + s delta`, `s in [-1,1]`, gives the closed form

```text
max_{[a_i,a_j]} |f| = |delta|^3 · max_{|s| <= 1} (1 - s^2) |s - beta| ,
mu(f_m) = 2 min( |m^3 - m - u w| , |m^3 - m + u w| ) ,  u = m^2 + 1/3, w^2 = u .
```

(The closed form agrees with the general instrument to `2.4e-15` relative on 60
random `m`.) Exact anchors: `Q(0) = 1` (the central-root cubic `z^3 - z`),
`Q(±i/sqrt 3) = 9/8` (the equilateral triangle, certified in exact rational
arithmetic in block 1 of the checker: `81/64 - |f|^2 = (27/16)s^2(5 - 4s^2 - 16s^4)`
on the chord, so the maximum `9/8` is attained **only** at the midpoint), and
`Q(m) -> 1` as `|m| -> infinity`.

A `500 x 500` scan of the closed quadrant `[0,6]^2` (both symmetries used) gives
`max Q = 1.12490` at `m = 0.5772 i ≈ i/sqrt 3` and **zero** grid points above
`9/8 + 1e-9`; on the ring `|m| = 6` the maximum is `1.00077`. Together with the
adversarial climbs of §7.1, which return exactly `1.125000` from all eleven seed
families:

```text
S_3 = 9/8   (measured; the lower bound S_3 >= 9/8 is exact).
```

The lower bound is a theorem; the upper bound is a measurement over a
two-real-parameter space and is **not** certified here (an interval-arithmetic
proof would have to handle an interior equality point at `m = i/sqrt 3`).

## 7. Measurement

Floating point; falsification evidence only.

### 7.0 Instrument and its guards

Segment maxima are computed from the **product form** `prod_j |z - a_j|` on a
grid plus ternary refinement — no coefficient expansion on the segment, no
inverse branches, no path tracking, so the saddle-connection wall class does not
apply. Agreement with `2 x 10^5`-point sampling: `2.2e-10` relative.

Two guards were added after they caught live artifacts, and both are load
bearing:

- **Lemma 0 guard.** `Q >= 1`, `R >= 1`, `S >= 1` are theorems. A first census
  pass reported `min Q = 3.2e-07` at `n = 10` together with `max R = 1.819` and
  `max S = 2.271`: those "leads" were instrument failure, and were discarded.
- **Newton-residual guard.** `mu` computed from `np.roots` of the expanded
  derivative loses relative precision when the root moduli span many orders. The
  guard is the defining identity `sum_j 1/(c - a_j) = 0`, tested against
  `sum_j 1/|c - a_j|` with tolerance `1e-7`, and critical values are evaluated
  in the product form. **This retracted two would-be counterexamples of this
  lane:** the geometric-progression scan reported `Q = 17.60` at `n = 12`
  (`r = 2.348`) and `Q = 36.63` at `n = 14` (`r = 1.828`); re-audited at 120
  digits with `mpmath` the true values are `Q = 1.0117` and `Q = 1.0181`, with
  `mu ≈ 6.05e-25` and `1.19e-24` — far below double-precision relative
  resolution. Both configurations have `R = S = 1`. Rejection rate of the guard
  on random draws: `0%` at `n = 4`, `1.5%` at `n = 8`, `7.5%` at `n = 12`,
  `14.5%` at `n = 20`, `44%` at `n = 40`; the rejected class is exactly the
  multi-scale cluster class, which Theorem 2 shows contributes only lower-degree
  values anyway.

Every reported maximiser below was re-audited with `mpmath` at 60 digits.

### 7.1 `sup Q` by degree (adversarial climbs, no disc constraint)

Hard-constrained hill climbs (infeasible proposals rejected outright), eleven
seed families — regular, jittered polygon, uniform disc, central-root,
two-level wall, pulled pair with a far cluster, near-collinear, cluster of
clusters, random concyclic, geometric progression ("spiral"), and
random-radii polygon — with multiple restarts per family per degree.

<!--TABLE_SUPQ-->

### 7.2 The near-extremal family

The climbs converge, at every degree `>= 4` reached, on the **geometric
progression**

```text
a_j = q^j ,   j = 0, ..., n-1 ,   q = r e^{i alpha} ,
```

equivalently the orbit of a circle rotation, laid on a logarithmic spiral. This
is a two-parameter family that reproduces the free-optimisation value to within
a few parts in a hundred at every degree, and the optimal `alpha` is **not**
`2 pi/n`: it is a multiple `alpha n/(2 pi) ≈ 1.0, 0.90, 1.04, 2.56, 4.95, 6.24,
2.04, 1.03` at `n = 3, ..., 10`, i.e. the roots are (near-)concyclic points whose
angular gaps take the three values of the three-distance theorem. That is the
structure that defeats a chord bound: no two roots close (which would give a
cheap chord) and no long chord passing near the centre (which is what makes the
regular polygon's diameter cheap).

<!--TABLE_GEOM-->

### 7.3 `R` and `S`: no violation anywhere

<!--TABLE_RS-->

### 7.4 Census

<!--TABLE_CENSUS-->

## 8. Routes tried here that failed, precisely

- **A local argument at the closest pair.** For the closest pair `a, b` at
  distance `delta`, every other root is outside both discs `D(a,delta)`,
  `D(b,delta)`, so it is at distance `>= delta sqrt(3)/2` from the midpoint `m`,
  and `f'/f (m) = H'/H (m)` with `|H'/H| <= 2(n-2)/(delta sqrt 3)`. Rouché
  against `1/(z-a) + 1/(z-b)` on `|z - m| = alpha delta` needs
  `2 alpha (sqrt3/2 - alpha) > (n-2)(alpha^2 + 1/4)`, whose left side has
  maximum `1.000` over `alpha`. So the argument produces a critical point near
  the midpoint only for `n = 2`. Improving the bound by the mutual separation of
  the other roots does not help: for a `delta`-separated set the sum
  `sum 1/|m - u_l|` is dominated by the *far* roots and grows like `sqrt n/delta`.
  This is the precise form of the obstruction flagged in
  [`MiddleRegimeCanonicalHub.md`](MiddleRegimeCanonicalHub.md) §6.
- **Phase-free bounds on the chord.** Writing
  `|f(z)| = |z-a||z-b| prod_{l>=3} |z - u_l|` and bounding each far factor by
  `|u_l|(1 + |z|/|u_l|) <= 2 |u_l|` gives `2^{n-2}`, useless. This is the same
  death as §7 of the hub-Taylor note and §7 of the middle-regime note: every
  phase-free estimate dies on the equality family, where the `n`-fold
  cancellation is the entire content.
- **Star-shapedness of `L_0` by a logarithmic-derivative sign.** `[c*,a] ⊂ L`
  for all rays would follow from `Re(z W'/W) >= 0` on `L_0`, i.e.
  `Re(z K'/K) >= -2` where `K = W/(z-c*)^2`. Using
  `Re(z/(z-k)) >= 1/2 iff |z| >= |k|` this holds whenever every other preimage
  `k` of `f(c*)` is no farther from the origin than `z`, which is the wrong way
  round: the other preimages are typically *outside* `L_0`. The sufficient
  condition reduces to `sum_i |k_i|/|z - k_i| <= n`, i.e. `L_0` inside the
  Voronoi cell of `c*` against the other preimages of `f(c*)` — true in every
  sample but not derivable from `d = 2` alone. **This is the smallest gap
  between the measurement and a proof of Conjecture S.**
- **The concyclic route.** `concyclic_alternation_theorem` (Theorem C′ of
  [`ConcyclicAlternation.md`](ConcyclicAlternation.md)) gives, for roots on a
  circle of radius `rho`, two adjacent roots with `max_{[a,b]} |f| <= 2 rho^n`.
  Converting that to `Q <= 2` needs `mu >= rho^n`, and `rho^n` is exactly the
  value `mu` takes on the regular polygon, which maximises it. So the concyclic
  theorem gives `Q <= 2 rho^n/mu >= 2`: **vacuous for Q_chord**. The concyclic
  case of Q_chord is not a corollary of the alternation theorem and needs its
  own argument.
- **Perturbation of the equality family.** Localising the critical points of a
  `delta`-perturbed regular `n`-gon inside `|z| <= r` by Rouché on
  `sum_j 1/(z - a_j)` versus `n z^{n-1}/(z^n - 1)` requires
  `delta < r^{n-1}(1-r-delta)^2/(1-r^n)`, whose optimum over `r` is
  `delta = O(1/n^2)` at `r = 1 - 1.6/n`, where the value estimate loses the
  factor `1 - r^n = 1 - e^{-1.6} = 0.798` and the bound `Q < 2` is lost. Pushing
  `r` down to `1/2` restores the value estimate but forces `delta = O(2^{-n})`.
  A perturbative theorem is therefore available only with an exponentially small
  explicit `delta_n`, and it says nothing that Theorem C of
  [`MiddleRegimeCanonicalHub.md`](MiddleRegimeCanonicalHub.md) does not already
  forbid extending. **Not landed; do not re-derive.**
- **The regular polygon as the extremal configuration.** False at every degree
  `>= 4` and in a stronger way than previously recorded: for even `n` the
  regular polygon has `Q = 1` *exactly* (diameter chord), the minimum possible
  value.

## 9. Claim boundary

Proved unconditionally, at every degree: Lemma 0 (`Q >= 1`); Theorem 1
(collinear roots give `Q = 1`); Theorem 2 (`S_n` is nondecreasing, with the
cluster construction); Theorem 3 (the 2-reduction, the lemniscate structure of
`L`, `R >= 1`, `S >= 1`, the two implications, and the necessary condition);
Theorem 4(a)–(d) (`R = 1` on the equality family and on the two-level wall,
`Q = 1` on the central-root family and on even-degree regular polygons,
`Q = 9/8` on the equilateral triangle).

Certified in exact arithmetic by the checker: the `9/8` chord reduction and its
Bernstein positivity certificate; the even-degree diameter identity for
`n = 4, ..., 24`; the central-root stationarity identity and critical-value
formula for `n = 3, ..., 12` (sympy); the two-level-wall inequality on 16 exact
rational `(k, a, b)` rows.

Measured only, with no universal authority: every number in §6's global scan and
in §7; `S_3 = 9/8` as an upper bound; the claim that `R` and `S` are never
`> 1`; the asymptotics of `S_n`. Two "counterexamples" produced inside this lane
(`Q = 17.60` at `n = 12` and `Q = 36.63` at `n = 14` on geometric progressions)
were **retracted** as instrument failure and are recorded in §7.0 as the seventh
and eighth specimens of that class in this directory.

Not proved: Conjecture Q_chord in either form; Conjecture R; Conjecture S;
`S < 2`; `S_3 <= 9/8`; and Erdős #1041. **No new `(n, mu)` cell is closed.**

## 10. Consumers

- [`MiddleRegimeCanonicalHub.md`](MiddleRegimeCanonicalHub.md): §6's Conjecture
  Q is this note's subject; §5 here supplies the framing correction (the
  constant is attained only at `n = 3`), §4 the sharp reduction, and §7 the
  extended measurement to `n = 30` with a retraction of that note's implicit
  reliance on unguarded float `mu`.
- [`ConcyclicAlternation.md`](ConcyclicAlternation.md): §8 records exactly why
  Theorem C′ does not reach Q_chord.
- [`CentroidVarianceChordChart.md`](CentroidVarianceChordChart.md): Theorem 1
  here is the `Q`-form of its collinear companion; Theorem 4(a) at `n = 3` is
  its Lemma 6.
- [`HyperbolicPackingArityFloor.md`](HyperbolicPackingArityFloor.md) /
  [`FixedDegreeClusterSeparationClosure.md`](FixedDegreeClusterSeparationClosure.md):
  the weak form would meet the `mu <= 2/5` closure at `1/2`.
- [`LowCriticalPotentialClosure.md`](LowCriticalPotentialClosure.md): Theorem 3
  is a second, hub-free route to a `2 mu` certificate and does not use the
  comparison ODE.
