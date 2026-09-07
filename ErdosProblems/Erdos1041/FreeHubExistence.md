# Erdős 1041: free-hub existence in the near-Fekete shell

Status, 2026-09-05 (wave 3, lane W3-C). Four ordinary theorems with proofs, one
exact identity, three exact Gaussian-rational certificates — including the first
positive resolution of the degree-five configuration that
[`HubTaylorSpokeCertificate.md`](HubTaylorSpokeCertificate.md) Theorem 4 uses to
kill the whole standing hub set — one falsified geometric hypothesis, two
refuted hub rules, **a refutation of the hub-Taylor criterion (A) itself as a
completion route**, and a sharp replacement conjecture with its lower half
proved. **Erdős #1041 is not proved here, and no part of the surviving regime
`2/5 < mu < 1` is closed.**

The one-line summary for the next lane: the free hub EXISTS everywhere it was
looked for, but the certificate that was supposed to detect it — criterion (A) —
is provably too coarse; the right objective is the value `mu`, and §8.2 proves
the matching lower bound.

Replay: `./repo-python scripts/check_erdos1041_free_hub_existence.py`

## 0. Authority boundary

* The criterion throughout is `HubTaylorSpokeCertificate.md`'s criterion (A) at
  a hub `h`: with `b_k = f^{(k)}(h)/k!` and `T_j(z) = sum_{k<=j} b_k (z-h)^k`,
  criterion (A) at a root `a` is `max_{0<=j<=n-1} |T_j(a)| < 1`. Theorem 2 of
  that note — (A) at two roots gives containment AND length `< 2`, with no
  metric clause — is used, not re-derived.
* `V(h) := min over root pairs {a,b} of max( max_j|T_j(a)|, max_j|T_j(b)| )`,
  i.e. the **second smallest** of the `n` numbers `max_j|T_j(a_i)|`. The **good
  set** is `G(f) = {h : V(h) < 1}`. `G(f) != empty` implies Erdős #1041 for `f`.
  The converse is false: (A) is strictly stronger than containment, so an empty
  `G` is **not** a counterexample to #1041. Section 8 depends on this.
* The inner-model reduction `f(rho Z) = rho^n Q(Z) + C` is
  [`NearFeketeInnerModelWidening.md`](NearFeketeInnerModelWidening.md)
  Proposition 1, used and not re-derived. Its widened scaling `(W)`
  (`eps_j ~ rho^{n-j}`) and the vacuity of admissibility in the cusp are that
  note's §3-§4.
* Sections 1-5, and Lemma S in §8.2, are proofs and exact certificates.
  Sections 6, 7, 8.1 and 8.3 are float measurement and are labelled as
  falsification evidence only.
* §1 and §2 are **restatements** of corpus property at a general hub, not new
  identities; see §1.3 for the attribution.

## 1. The criterion is a statement about tails

Let `f` be monic of degree `n`, `h` any point, `a` a root, `zeta = a - h`,
`b_k = f^{(k)}(h)/k!` (so `b_n = 1`, `b_0 = f(h)`).

> **Lemma T (tail form).** For `0 <= j <= n-1`,
>
> ```text
> T_j(a) = - sum_{k=j+1}^{n} b_k zeta^k .
> ```
>
> Hence criterion (A) at `h` for the root `a` is equivalent to
>
> ```text
> max_{1 <= i <= n} | sum_{k=i}^{n} b_k zeta^k |  <  1 .
> ```
>
> *Proof.* `sum_{k=0}^{n} b_k zeta^k = f(a) = 0`, so the head `T_j(a)` is minus
> the tail. ∎

Two ends of the range are free of content:

* `i = n`: `|zeta|^n < 1`, i.e. `|a - h| < 1` — the free-length clause of
  Theorem 2, recovered.
* `i = 1`: `|f(h)| < 1` — the hub must be inside the sublevel set.

So the substance of (A) is the `n-2` intermediate tails, and each of them is
`zeta^n` plus a correction built from `b_{n-1}, ..., b_i`.

### 1.1 The centroid is exactly where the top correction dies

`b_{n-1} = f^{(n-1)}(h)/(n-1)! = n(h - h_0)` where `h_0 = (1/n) sum_j a_j` is the
root centroid. So:

> **Corollary C (centroid collapse).** At `h = h_0`,
>
> ```text
> b_{n-1} = 0 ,      T_{n-2}(a) = T_{n-1}(a) = -(a-h_0)^n ,
> ```
>
> and criterion (A) at the centroid reduces to
>
> ```text
> |f(h_0)| < 1 ,   |a - h_0| < 1 ,   and   max_{1<=j<=n-3} |T_j(a)| < 1 .
> ```
>
> At `n = 3` the last family is **empty**, so at a cubic the centroid criterion
> is exactly "the hub is in the sublevel set and the root is within `1`". At
> `n = 4` it adds only `j = 1`.

This is the structural reason for the corpus's own measurement
(`HubTaylorSpokeCertificate.md` §4, reading 3) that the centroid wins 82-89% of
covered cases from `n = 6` up, against the corpus's default hub ordering: the
centroid is the unique point at which two of the `n` truncation tests collapse
onto the free one.

### 1.2 Danger is at the hub end of the spoke, not the root end

Write `sigma_i = sum_{j=1}^{n-i} b_{n-j} zeta^{-j}`, so that
`sum_{k=i}^{n} b_k zeta^k = zeta^n (1 + sigma_i)`. Criterion (A) becomes

```text
|1 + sigma_i| < |zeta|^{-n}   for i = 1..n ,
```

i.e. **all `n` partial sums of the sequence `(b_{n-j} zeta^{-j})_{j>=1}` lie in
the disc `|1 + S| < |zeta|^{-n}`**, with `sigma_n = 0` at one end and
`|1 + sigma_1| = |f(h)|/|zeta|^n` at the other. In the near-Fekete shell
`|zeta|^{-n} = 1 + O(1-|zeta|)` is barely above `1`, the partial sums start at
`0`, and the binding constraint is on the FIRST few partial sums — the terms
carrying the highest-order Taylor coefficients, which is the hub end of the
spoke. This is the "danger zone is near the hub" picture in tail coordinates.

### 1.3 What was already corpus property

Lemma T is the Abel/tail rearrangement of
`abel_control_polygon_and_all_degree_trinomial_conclusion` (the `h = 0` case)
and of `HubTaylorSpokeCertificate.md` Lemma 1 (the head form at a general hub);
the only new thing is reading it from the tail end, which is what makes
Corollary C and §2-§3 one line each. The free length `|T_{n-1}(a)| = |a-h|^n`
is that note's §1.3. `GeneralSpokeIdentity.md` owns the critical-hub case.

## 2. Theorem A: the Form-A family is closed by the origin hub, at every degree

> **Theorem A.** Let `n >= 3` and let
>
> ```text
> f(z) = z^n + gamma z^{n-2} + c_0
> ```
>
> be monic with all roots in the open unit disc (`gamma, c_0` arbitrary
> complex). Then at `h = 0`, for **every** root `a`,
>
> ```text
> max_{0<=j<=n-1} |T_j(a)| = max( |c_0| , |a|^n ) < 1 .
> ```
>
> Consequently criterion (A) holds at the origin for all `n` roots, and Erdős
> #1041 holds for `f` by a two-spoke broken line through the origin of length
> `< 2`.
>
> *Proof.* At `h = 0` the Taylor coefficients are `b_0 = c_0`,
> `b_{n-2} = gamma`, `b_n = 1` and `b_k = 0` otherwise. By Lemma T the tail from
> `i` is `zeta^n` for `i in {n-1, n}` and `zeta^n + gamma zeta^{n-2} = -c_0` for
> `1 <= i <= n-2`. The two values are `|a|^n` and `|c_0| = prod_j |a_j| `. Both
> are `< 1` because every root is in the open disc. ∎

Note `c_{n-1} = 0`, so the origin **is** the root centroid here and Theorem A is
Corollary C with the extra observation that the remaining truncations are
constant. Theorem A contains `z^n - m` (`gamma = 0`), which is the equality
family of `capacity_geodesic_conjecture_and_its_equality_family`, and is affine
invariant.

*Attribution.* The general shape — "if the Taylor coefficients at `h` are
supported on `{0, q, n}` then (A) holds at `h` with value
`max(|f(h)|, |a-h|^n)`" — is the translated-trinomial statement already carried
by `abel_control_polygon_and_all_degree_trinomial_conclusion` and by the
`translated trinomials (m <= n-2)` row. What §2 adds is the observation that
`q = n-2` is exactly the **tied Newton face / Form A** direction the wave was
asking about, so that direction of the near-Fekete cusp is not merely covered
but covered with the exact criterion value.

*Verification.* Independently of the exact replay, a float sweep of the family
over `418,400` admissible configurations (`gamma` on 100 values in
`[0, 2.5] u [1e-6, 1]`, `|c_0|` on 70 values in `[0, 1.6]`, `arg c_0` on 36
values, degrees `4..8`, rejecting any configuration with a root of modulus
`>= 1`) produced **zero** origin-hub failures at every degree, with the worst
value equal to `|c_0|` to all printed digits — as Theorem A predicts.

## 3. Theorem B: near-Fekete existence at the centroid, with the explicit relation

> **Theorem B.** Let `f` be monic of degree `n >= 3` with all roots in the open
> unit disc. Let `h_0` be the root centroid, `b_k = f^{(k)}(h_0)/k!`, and put
>
> ```text
> m = |f(h_0)| = prod_j |a_j - h_0| ,     E = sum_{k=1}^{n-3} |b_k|
> ```
>
> (`E = 0` when `n = 3`). If
>
> ```text
> (i)  m + E < 1 ,   and
> (ii) |a_j - h_0| < 1 for at least two roots a_j ,
> ```
>
> then criterion (A) holds at `h_0` for those two roots, so the broken line
> `a -> h_0 -> b` lies in `{|f| < 1}` and is shorter than `2`, and Erdős #1041
> holds for `f`.
>
> *Proof.* Fix such a root `a`, `zeta = a - h_0`, `|zeta| < 1`. For
> `j in {n-2, n-1}`, `|T_j(a)| = |zeta|^n < 1` by Corollary C. For
> `0 <= j <= n-3`,
> `|T_j(a)| = |b_0 + sum_{k=1}^{j} b_k zeta^k| <= m + sum_{k=1}^{n-3}|b_k| = m + E`
> because `|zeta| < 1`. ∎

**The point is which coefficients are absent from `E`.** The naive Abel bound
requires `m + sum_{k=1}^{n-1}|b_k| < 1`. Theorem B drops `k = n-1` (killed by
the choice of hub) and `k = n-2` (killed by the collapse), so the top two
perturbation directions of the near-Fekete family are **unconstrained**.

**The explicit relation asked for.** Write `f` in centroid coordinates as
`f(z) = z^n - m_0 + sum_{k=0}^{n-2} eps_k z^k`. Then Theorem B reads

```text
sum_{k=1}^{n-3} |eps_k|  <  1 - |f(h_0)| ,
```

with `eps_{n-2}` free. In the widened inner-model scaling `(W)` of
`NearFeketeInnerModelWidening.md` §3 — `eps_{n-j}` of order `rho^j`, `rho` the
critical-cluster scale — the left side is of order `rho^3` while
`1 - |f(h_0)|` is of order `rho^2` in the balanced cusp. **So Theorem B closes
the whole balanced near-Fekete cusp, at every degree, and stops exactly at the
deep corner `1 - |f(h_0)| = O(rho^3)`.**

*Certified* (exact replay, check `near_fekete_centroid`): six stored
Gaussian-rational near-Fekete configurations at degrees `4..9`, of the form
`a_j = r (w^j + eps conj(w^j))` with `r = 0.9999` and `eps` at `0.999` of the
largest value keeping every root inside the disc, with

| `n` | `mu` | `m` (upper) | `E` (upper) | `max_j |T_j|^2` on the pair |
|---|---|---|---|---|
| 4 | 0.9995999737 | 0.9995999737 | `5.4e-20` | 0.9999990463 |
| 5 | 0.9995001284 | 0.9995001288 | `8.2e-08` | 0.9999990463 |
| 6 | 0.9994001306 | 0.9994001306 | `9.0e-08` | 0.9999985695 |
| 7 | 0.9993001790 | 0.9993001790 | `4.2e-07` | 0.9999983311 |
| 8 | 0.9992002558 | 0.9992002558 | `3.5e-07` | 0.9999980927 |
| 9 | 0.9991003918 | 0.9991003928 | `4.8e-07` | 0.9999976158 |

Every one of these has `mu > 0.999`, i.e. sits deep inside the surviving regime
that `HyperbolicPackingArityFloor.md` cannot reach.

**The improvement over the naive bound is exercised inside the surviving
regime.** On the symmetric ellipse family above the naive bound happens to hold
too (`m + sum_{k<n}|b_k| = 0.9999995..0.9999998`, just under `1`), because there
the disc constraint forces `|b_{n-2}| <~ 1 - m`. That is an accident of the
family. Six Gaussian-rational configurations, one per degree `4..9`, all with
roots in the open unit disc, are stored in the replay (`theorem_b_strict_gain`)
and verified exactly: Theorem B's hypothesis holds, the naive bound fails, and
the conclusion is checked directly.

| `n` | `mu` | `m + E` (upper bound) | naive `m + sum_{k<n}|b_k|` (lower bound) | `max_j |T_j|^2` on the pair |
|---|---|---|---|---|
| 4 | 0.99842 | 0.99894 | 1.00451 | 0.99883 |
| 5 | 0.99607 | 0.99880 | 1.00257 | 0.99804 |
| 6 | 0.99299 | 0.99615 | 1.00222 | 0.99844 |
| 7 | 0.99036 | 0.99891 | 1.00292 | 0.99454 |
| 8 | 0.98708 | 0.99627 | 1.00261 | 0.98491 |
| 9 | 0.98341 | 0.99840 | 1.00495 | 0.97273 |

All six have `mu > 0.98`, deep in the surviving regime. So dropping `k = n-1`
and `k = n-2` from the sum is not cosmetic: it is the difference between the
bound firing and not firing on a positive-measure set of the shell.

**Hypothesis (ii) is not automatic.** `prod_j |a_j - h_0| = m < 1` gives at
least one root within `1` of the centroid, not two. A sufficient condition is
`Var := (1/n) sum_j |a_j - h_0|^2 < 1 - 1/n` (if `n-1` roots were at distance
`>= 1` then `n Var >= n-1`), but that condition is useless in the near-Fekete
shell, where `Var -> 1`. At `n = 3` the hypothesis genuinely fails: the shifted
configuration `w = (e^{i beta}, e^{-i beta}, -2 cos beta)` with
`cos^2 beta < 3/8` has two `|w_j| = 1` and satisfies the diameter constraint,
so only one root is within `1` of the centroid, while `m = 2|cos beta| < 1`.
Cubics are closed elsewhere (`cubic_minimal_critical_value_short_hub`).

## 4. Lemma R: the `n`-ray coupling identity at a free hub

> **Lemma R.** Let `f` be monic of degree `n`, `w = e^{2 pi i / n}`. For every
> `h` and every `xi`,
>
> ```text
> sum_{l=0}^{n-1} f(h + w^l xi)  =  n ( f(h) + xi^n ) .
> ```
>
> In particular, if `f(h) != 0`, `theta = arg f(h)`, and `phi` is chosen with
> `e^{i n phi} = -e^{i theta}`, then for every `r >= 0`
>
> ```text
> sum_{l=0}^{n-1} Re( e^{-i theta} f(h + r w^l e^{i phi}) ) = n ( |f(h)| - r^n ).
> ```
>
> *Proof.* `f(h + X) = sum_k b_k X^k` and `sum_{l<n} w^{l k} = n` when `n | k`
> and `0` otherwise; only `k = 0` and `k = n` survive, and `b_n = 1`. ∎

This is the free-hub form of the Vieta coupling that
[`CapacityGeodesicConjecture.md`](CapacityGeodesicConjecture.md) §5 states for
the `n` inverse branches (`sum_j z_j(w)^k = const` for `k <= n-1`). Two
readings:

* the descending direction is *shared*: along the `n` rays from ANY hub in the
  `n` directions where `-e^{-i theta} X^n` is negative, the mean of
  `Re(e^{-i theta} f)` is `|f(h)| - r^n`, so at radius `r = |f(h)|^{1/n}` the
  mean is exactly `0` and at least one direction is descending;
* **and this is all it gives.** The identity is one linear functional per
  radius. The direction realising the mean can change with `r`, so Lemma R
  cannot by itself produce a single direction that is good for all `r`, still
  less two. Any use of it must be coupled to a monotonicity or convexity
  statement in `r`, which I do not have.

The exact replay verifies Lemma R over `Q(i)` at `n = 2` and `n = 4`, where the
roots of unity are Gaussian rational; the general case is the displayed one-line
proof and is not a numerical claim.

### 4.1 Instrument note: the `t -> 0` inner limit is the wrong model for Form A

In the inner model, `|f| < 1` on a spoke becomes
`W(H + w) := Re(e^{-i theta} Q(H+w)) < t` with `t = (1 - |C|^2)/(2|C| rho^n)`.
Setting `t = 0` (the deepest cusp) and taking `Q = Z^n + gamma_{n-2} Z^{n-2}`
makes exactly `#{l : Re(gamma_{n-2} e^{-2 i phi_l}) >= 0} >= ceil(n/2)` of the
`n` root directions good at `H = 0`. That count is correct but the model is
wrong for this family: for `f = z^n + gamma z^{n-2} + c_0` the disc constraint
forces `t` of order `1`, not `t -> 0`, and Theorem A then makes **all** `n`
directions good. **Anyone optimising in the inner model must carry `t` as a live
parameter; setting `t = 0` throws away precisely the margin that closes Form A.**
Together with the saddle-connection wall guard
(`NearFeketeInnerModelWidening.md` §5.4 and its withdrawal), that is the second
recorded way this lane's inner model manufactures false negatives.

## 5. Exact free-hub certificates at the configurations that defeat every fixed hub

`HubTaylorSpokeCertificate.md` Theorem 4 exhibits a monic quintic, all roots
strictly inside the disc, `mu > 0.999987`, at which **no** point of
`H = {c*} u {critical c : |f(c)| < 1} u {0} u {centroid}` carries two contained
straight spokes; the note records only float evidence (criterion value
`0.99998752`) for a free hub near `-0.05 - 0.09i`. The same file pins two
further witnesses at degrees six and nine.

> **Certificate 5.1 (exact).** With the five roots of `QUINTIC_HUB_SET_WITNESS`
> (IEEE-754 hexadecimal literals, read from
> `scripts/check_erdos1041_hub_taylor_spoke_certificate.py` by AST and asserted
> byte-equal), take the Gaussian-rational hub
>
> ```text
> h = (-459 + 1167 i) / 16384 .
> ```
>
> In exact `Fraction` arithmetic, the roots indexed `1` and `2` satisfy
> `max_{j<5} |T_j|^2 = 0.9999984799041575 < 1`, with margin `1.52e-06`, and the
> broken line has length at most `1.87843567 < 2`. Every decision is a
> comparison of exact rationals; the length bound uses `isqrt`-derived rational
> upper bounds with 64 fractional bits.

> **Certificate 5.2 (exact).** The pinned degree-six witness passes at
> `h = (1178 + 806 i)/16384` (roots `0, 1`, `max |T_j|^2 = 0.9999425179`,
> margin `5.75e-05`, length `<= 1.8515941`), and the pinned degree-nine witness
> at `h = (-2056 - 1670 i)/16384` (roots `5, 6`,
> `max |T_j|^2 = 0.9999259434`, margin `7.41e-05`, length `<= 1.6997988`).

Certificate 5.1 is the substantive one: it is the first exact positive
resolution of the configuration `HubTaylorSpokeCertificate.md` §2b uses to kill
the hub rule, and it converts that note's float remark into a certificate. What
it does **not** do is restore a rule — the hub was found by search, and §7 shows
that the obvious canonical widening of the hub set does not contain it in
general.

A structural feature of all three certificates: in each case the maximum
`max_j |T_j(a)|` is attained at `j = 0` for both roots, i.e. `|T_j(a)| <= |f(h)|`
for every `j`. The good hub is a point where the whole truncation ladder is
dominated by the hub value.

## 6. The good set `G(f) = {h : V(h) < 1}` — measured

Floats; falsification evidence only. `V(h) >= |f(h)|` always (take `j = 0`), so
`G(f)` is contained in the sublevel set `{|f| < 1}`.

| configuration | `n` | `mu` | `rho_crit` | `V(0)` | `V(centroid)` | `V(c*)` | `min_h V` | `|h* - c_cluster| / rho_crit` |
|---|---|---|---|---|---|---|---|---|
| Theorem-4 quintic | 5 | 0.99998752 | 0.11756 | 1.0001358 | 1.0001361 | 1.0089728 | **0.99999923** | 0.652 |
| pinned degree six | 6 | 0.99995099 | 0.17050 | 0.9999991 | 0.9999991 | 1.0146105 | 0.99997122 | 0.511 |
| pinned degree nine | 9 | 0.99994148 | 0.28239 | 0.9999987 | 0.9999934 | 1.0092159 | 0.99996294 | 0.573 |
| `z^n - m`, `m = 0.999` | 4..10 | 0.999 | — | 0.999 | 0.999 | 0.999 | 0.999 | 0 |
| `z(z^{n-1} - r^{n-1})`, `r = 1-1e-4` | 4..10 | 0.472..0.696 | 0.63..0.77 | 0.9990..0.9996 | same | 0.472, 0.802, 1.164, 2.064, 3.248, 6.925 | 0.472..0.944 | 0.79..1.00 |

Readings.

1. **The `c*` hub is the worst canonical choice at both ends of the shell.** On
   the central-root family `z(z^{n-1}-r^{n-1})` — which is not near-regular, has
   `mu -> 1` as `n` grows, and whose natural hub is the central ROOT — the least
   critical point gives `V(c*) = 1.16, 2.06, 3.25, 6.93` at `n = 6, 7, 8, 10`,
   while the origin gives `V = 1 - n*10^{-4}`. The origin/centroid covers that
   family at every degree tested.
2. **The `z^n - m` family has an open good set of a fixed shape.** `V ≡ m` in a
   neighbourhood of the origin; on a box of half-width `10 rho_crit` the good
   fraction is `1.00, 1.00, 0.96, 0.77, 0.48, 0.35` at `n = 5..10`, so the good
   set is comparable to but not much larger than the critical-cluster scale once
   `n >= 7`.
3. **The hypothesis "`G(f)` contains a disc of radius `c rho_crit` around a
   computable centre" is FALSE.** At the three hard witnesses `G(f)` is a thin
   sliver, not a disc: measuring by ray bisection from the float optimum `h*`
   over 24 directions,

   | witness | inradius | outradius | `inradius / rho_crit` | `sqrt((1-mu)/binom(n,2))` |
   |---|---|---|---|---|
   | quintic | `5.19e-06` | `4.69e-03` | `4.4e-05` | `1.12e-03` |
   | degree six | `7.94e-05` | `6.58e-02` | `4.7e-04` | `1.81e-03` |
   | degree nine | `7.85e-04` | `1.26e-01` | `2.8e-03` | `1.27e-03` |

   The **width** of the good set scales like `sqrt((1-mu)/binom(n,2))` (the
   quadratic response of `b_{n-2}(h) = binom(n,2) h^2 + c_{n-2}` against the
   margin `1 - mu`), not like `rho_crit`; it is `rho_crit` that sets the
   **position**. What is stable across the three witnesses is
   `|h* - c_cluster| / rho_crit = 0.652, 0.511, 0.573`, i.e. the good hub sits
   at roughly half the critical-cluster radius from its centre.
4. Of the candidate centres in the lane brief, the "Fekete/balance point"
   `sum_j (a_j - h)/|a_j - h|^2 = 0` is **not a new point**: that equation is
   `conj(- f'(h)/f(h)) = 0`, i.e. `h` is a critical point of `f`. It is already
   in the refuted fixed hub set.
5. In the surviving regime the free hub sits at a fraction
   `0.21 .. 0.48` (median, by degree) of `rho_crit` from the critical-cluster
   centre across the configurations of §8; the position statement is stable, the
   size statement is not.

## 7. The derivative-tree hub rule, and its refutation

The two canonical hubs that work — the centroid (`= the root of f^{(n-1)}`) and,
on the quintic, a root of `f^{(2)}` — suggest one canonical widening:

```text
H_D(f) = union over k = 1..n-1 of the root set of f^{(k)}     ( n(n-1)/2 points )
```

which contains the critical points (`k = 1`) and the root centroid (`k = n-1`),
and which is affine covariant. `H_D` does cover all three hard witnesses on
file: the quintic through a root of `f''` (`V = 0.99999979`, at
`0.032 rho_crit` from the float optimum), the degree-six and degree-nine
witnesses through the centroid.

**It is refuted as a rule.** Over `1400` random survivors with `mu > 2/5`
(200 per degree, `n = 4..10`, four families: uniform in the disc, near-regular
with perturbation `1e-6..1e-1`, deep near-Fekete `1e-8..1e-3`, common-modulus
circle; colliding critical points rejected), `min_{h in H_D} V(h) >= 1` at

```text
n  =   4    5    6    7    8    9   10
fail   0   19    8    8    6    5    2        (worst V = 1.00279 at n = 5)
```

So a `n(n-1)/2`-point canonical hub set fails at every degree from five up, at a
rate of a few per cent. This strengthens `HubTaylorSpokeCertificate.md`
Theorem 4 from "the four-point hub set dies at one configuration" to "the
`n(n-1)/2`-point derivative tree dies at a positive fraction of the surviving
regime". Any completion must move the hub off every canonical algebraic set of
this kind, or replace criterion (A) by something weaker.

## 8. Wall-guarded search for an empty good set: open leads

Instrument. The objective is a direct polynomial evaluation, so the
inverse-branch saddle-connection defect class does not apply; the guard actually
needed here is different and is stated first.

> **Guard (good-set resolution).** `G(f)` can be a sliver of inradius `5e-06`
> (§6). A grid search that reports `min_h V >= 1` is therefore worthless unless
> its finest resolution is far below that. The searches below use a
> multi-scale zoom (6 levels, final spacing `~3e-10`) seeded from the canonical
> hubs, plus Nelder-Mead polish from every seed, plus — for the leads — a
> single-shot `1401 x 1401` global grid over `[-1.15R, 1.15R]^2` with
> Nelder-Mead polish from the best 40 cells. A greedy multi-scale zoom follows
> one basin and **can miss a sliver elsewhere**; that is why the leads below are
> leads and not results.

Taking the `H_D` failures of §7 as seeds (they are the configurations where the
canonical hubs are already exhausted), the free-hub minimisation returns
`min_h V >= 1` on

```text
n                      5     6     7     8
H_D failures collected 25    25    25    25      (from 307, 890, 522, 1087 survivors)
free hub resolves      22     6    17    11
UNRESOLVED              3    19     8    14      (worst min_h V = 1.00005, 1.00085, 1.00001, 1.00012)
```

(The worst values above are over ALL collected leads; the six audited per degree
in §8.1 reach `1.00025` at `n = 6` and `1.00012` at `n = 8`.) These are **leads for an empty `(A)`-good set**, and — critically — **not
counterexamples to Erdős #1041**, because criterion (A) is strictly stronger
than containment: `HubTaylorSpokeCertificate.md` §4 reading 1 already records 69
configurations where (A) fails at every hub of its set while every spoke is
still contained.

### 8.1 The audit: criterion (A) is too strong, and the geometric statement survives

Twenty-one of the leads (three at `n = 5`, six each at `n = 6`, `n = 7` and
`n = 8`) were re-audited against the weaker **geometric** test:

```text
(FH-geo)  exists h and two roots a, b with |a-h| < 1, |b-h| < 1, and
          max over [h,a] u [h,b] of |f|  <  1 .
```

On a `1401 x 1401` global grid over `[-1.15R, 1.15R]^2` with 257-point segment
sampling and Nelder-Mead polish from the best 40 cells, **all twenty-one pass
(FH-geo)** while all twenty-one fail criterion (A) at every hub. More than that:
the optimal geometric value is `mu` to six to eight digits in every case.

| lead | `n` | `mu` | `min_h V` (criterion A) | `min_h` two-spoke `max|f|` |
|---|---|---|---|---|
| n5_u0 | 5 | 0.9999703315 | 1.0000034554 | 0.9999703393 |
| n5_u1 | 5 | 0.9999987902 | 1.0000060216 | 0.9999987895 |
| n5_u2 | 5 | 0.9999809686 | 1.0000491356 | 0.9999809748 |
| n6_u0 | 6 | 0.9999985155 | 1.0000130710 | 0.9999985251 |
| n6_u1 | 6 | 0.9999921039 | 1.0000240586 | 0.9999921402 |
| n6_u2 | 6 | 0.9998858244 | 1.0002545259 | 0.9998858214 |
| n6_u3 | 6 | 0.9999914375 | 1.0000150199 | 0.9999914657 |
| n6_u4 | 6 | 0.9999683330 | 1.0000266673 | 0.9999683597 |
| n6_u5 | 6 | 0.9999800140 | 1.0000323612 | 0.9999800520 |
| n7_u0 | 7 | 0.9999948707 | 1.0000119915 | 0.9999949245 |
| n7_u1 | 7 | 0.9999968332 | 1.0000006427 | 0.9999968783 |
| n7_u2 | 7 | 0.9998477406 | 1.0000091194 | 0.9998484217 |
| n7_u3 | 7 | 0.9999993867 | 1.0000021956 | 0.9999993983 |
| n7_u4 | 7 | 0.9999959154 | 1.0000065761 | 0.9999959734 |
| n7_u5 | 7 | 0.9999992013 | 1.0000009776 | 0.9999992152 |
| n8_u0 | 8 | 0.9999788304 | 1.0000002716 | 0.9999792030 |
| n8_u1 | 8 | 0.9999973792 | 1.0000028214 | 0.9999974465 |
| n8_u2 | 8 | 0.9999979837 | 1.0000086073 | 0.9999980541 |
| n8_u3 | 8 | 0.9999572457 | 1.0000323765 | 0.9999574987 |
| n8_u4 | 8 | 0.9997283691 | 1.0001189894 | 0.9997285493 |
| n8_u5 | 8 | 0.9997874343 | 1.0000688220 | 0.9997885038 |

**Reading: criterion (A) is refuted as a completion route.** It fails at every
hub on a measurable set of the surviving regime (§7 plus these leads), and it
fails by `2.7e-7` to `2.5e-4` at configurations where the geometric statement
holds with margin `1 - mu`. The corpus's own remark that (A) is "lossy, not
violated as a geometric claim" is now quantified at a free hub. Any completion
must use `(A*)`, or containment `(E)` directly.

### 8.2 The value `mu` is exactly right, and the lower half is proved

> **Lemma S (sharp lower bound; first-merge level, corpus property).** Let `f`
> be monic of degree `n`, `mu = min_c |f(c)|` over critical points. For any
> point `h` and any two distinct roots `a, b`, the broken line
> `a -> h -> b` satisfies `max |f| >= mu`.
>
> *Proof.* Suppose `max |f| < t` on the broken line `Gamma`. `Gamma` is
> connected, so it lies in one connected component `C` of `{|f| < t}`. Every
> component of `{|f| < t}` is simply connected (if a closed curve lay in `C`,
> the maximum principle puts its interior in `C` too), and `f : C -> D(0,t)` is
> proper and holomorphic, hence a branched cover of degree `k = ` number of
> zeros of `f` in `C` counted with multiplicity. `Gamma` contains the two
> distinct roots `a, b`, so `k >= 2`, and Riemann-Hurwitz gives `k - 1 >= 1`
> critical points of `f` in `C`. Any such `c` has `|f(c)| < t`, so `t > mu`. ∎

Lemma S says the geometric objective of §8.1 is bounded below by `mu`, and the
measurements say it **equals** `mu` to eight digits at every audited
configuration, at `V(0) = m` on all of Form A (§2), and at
`2 cap{|f| <= mu}` on `z^n - lambda`. So the free-hub problem has a sharp value
and it is the first-merge level.

### 8.3 What could not be certified

I could not certify an empty good set exactly, and did not need to: nothing was
found to certify. For the record, the obstruction is that `V` is Lipschitz in
`h` with a constant growing like `n 3^{2n}` on the relevant region, so a
Lipschitz-covering certificate of `min_h V >= 1` over `{|f| < 1}` is far out of
reach; an exact emptiness certificate needs a global argument (a barrier on
`{|f| < 1}`, or an argument-principle count), not a finer sampler. **No value
above `1` in §7 or §8 is claimed as a refutation of Erdős #1041 or of the free
hub; they refute criterion (A) only.**

## 9. Claim boundary

**Proved unconditionally, with proofs in this note and exact replay:** Lemma T
and Corollary C (restatements of corpus property at a general hub); Theorem A
(the Form-A family `z^n + gamma z^{n-2} + c_0` is closed by the origin hub at
every degree, with the exact criterion value); Theorem B (the near-Fekete
centroid closure `m + E < 1` with `E` omitting `k = n-2` and `k = n-1`, and its
explicit shell relation `sum_{k<=n-3}|eps_k| < 1 - |f(h_0)|`); Lemma R.

**Certified exactly on named configurations:** the three free-hub certificates
of §5, including the Theorem-4 quintic; the six near-Fekete Theorem-B rows of
§3 at `mu > 0.999`.

**Measured only (floats, falsification evidence):** everything in §6, §7, §8,
and the 418,400-configuration Form-A sweep of §2 (which is corroboration of a
theorem, not its support).

**Refuted:** the hypothesis that `G(f)` contains a disc of radius
`c rho_crit` around a computable centre (§6.3); the derivative-tree hub rule
`H_D` (§7); the reading of the balance point as a new candidate hub (§6.4);
**criterion (A) as a completion route for the surviving regime** (§8.1) — it
fails at every hub on a positive fraction of survivors with `mu > 2/5`, at
configurations where the geometric statement holds with the full margin
`1 - mu`.

**Not proved:** Erdős #1041; free-hub existence in general; any part of the
surviving regime `2/5 < mu < 1` beyond what Theorem B's inequality covers.

**Smallest open sub-statement handed on.**

> **(FH) Free-hub geodesic-value conjecture.** For every monic `f` of degree
> `n >= 2` with all roots in the open unit disc, and every `eps > 0`, there is a
> point `h` and two distinct roots `a, b` with
>
> ```text
> |a - h| < 1 ,   |b - h| < 1 ,   and   max over [h,a] u [h,b] of |f|  <  mu + eps .
> ```

`(FH)` implies Erdős #1041 whenever `mu < 1`, with two straight spokes of total
length `< 2`, and it is **sharp**: Lemma S proves the matching lower bound
`>= mu`, and equality holds on `z^n - lambda`. It is the straight-spoke free-hub
analogue of `capacity_geodesic_conjecture_and_its_equality_family` with the
capacity replaced by the value, and unlike the `(A)` form it is not refuted by
anything on file: it holds at every one of the twenty-one audited §8 leads (with
the value equal to `mu` to seven or eight digits), at all three hard witnesses,
and on both pinned QC witnesses. On Form A, Theorem A gives the weaker
*containment* form with value `max(|c_0|, R^n)`, which for `gamma != 0` and
`n >= 4` is at least `|f(0)| >= mu` and so does **not** settle the sharp value
there; that is one concrete place to test `(FH)` first.

Two smaller reductions of `(FH)` that would already move the corpus:

* the `|a-h| < 1` clause. In `(A)` it was free (`|T_{n-1}(a)| = |a-h|^n`); in
  `(FH)` it is a hypothesis. Is it implied by the value clause?
* the quantitative shape. §6 says the `(A)`-good set has width
  `~ sqrt((1-mu)/binom(n,2))` and sits at `~ rho_crit/2` from the
  critical-cluster centre (`0.51, 0.57, 0.65` at the three witnesses). If the
  `(FH)`-good set has the same position law with a radius bounded below by
  `c_n sqrt((1-mu)/binom(n,2))`, `(FH)` follows by a fixed-point or degree
  argument on a disc of that radius; supplying the radius is the whole problem.

## 10. What was tried and failed, precisely

* **The `t -> 0` inner-model limit.** It gives only `ceil(n/2)` good root
  directions on Form A, while the exact statement (Theorem A) gives all `n`.
  The limit discards the margin. Do not re-run an inner-model optimiser with
  the threshold set to zero.
* **Killing `b_{n-2}` by hub choice.** `b_{n-2}(h) = 0` means
  `f^{(n-2)}(h) = 0`, a quadratic, so there are exactly two such hubs. They work
  on the quintic (`V = 0.99999979`) and fail on both pinned witnesses
  (`V = 1.00194, 1.00163`). Killing the leading correction is not enough because
  the lower ones (`b_{n-3}, ...`) are of the same order as the margin in the
  deep corner.
* **The absolute-value bound with all coefficients.** `m + sum_{k<n}|b_k| < 1`
  is what Theorem B improves on; on the three hard witnesses its value is
  `1.00344, 1.00249, 1.00135` against margins `1 - m` of `3.4e-08, 9.3e-07,
  6.6e-06`, i.e. lossy by factors `1e5, 2.7e3, 2.1e2`. **No triangle-inequality
  route reaches the deep corner**, at any hub; the phases are the entire
  content there. This is the §3-ceiling analogue of
  `HubTaylorSpokeCertificate.md` Proposition 3.
* **The "balance point"** `sum_j (a_j - h)/|a_j - h|^2 = 0` is a critical point
  (§6.4) and adds nothing.
* **Lemma R alone.** It is one linear functional per radius; it cannot pin a
  direction that is good for all radii. Do not attempt a per-direction
  conclusion from it without a monotonicity input.
