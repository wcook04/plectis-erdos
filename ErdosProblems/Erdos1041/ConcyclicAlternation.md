# Erdős #1041 for concyclic zeros: a Chebyshev alternation on the circle

Status, 2026-08-24: one complete sharp theorem, one complete lemma, one
unconditional corollary settling Erdős #1041 for a new class, and one calibrated
conjecture.  Erdős #1041 itself remains open; nothing below claims otherwise.

This is the circle companion to [CollinearRootCase.md](CollinearRootCase.md).
That note proves the sharp theorem for zeros on a **line** by Chebyshev
alternation against `T_n`.  The alternation there is available because a
polynomial with real zeros is real on the line.  The same argument runs on a
**circle**, because a polynomial with zeros on a circle is *self-inversive*, and
a self-inversive polynomial is a fixed unimodular function times a **real**
function of the arc parameter.  The comparison polynomial is `z^n - c` in place
of `T_n`, and the sharp constant is `2` in place of `C_n`.

The two notes together cover every configuration whose zeros lie on a circle or
a line — the whole Möbius-concyclic family.

## 1. Statement

Throughout, `w_1, …, w_n` are **distinct** points of the unit circle,

```text
g(z) = prod_{k=1}^n (z - w_k),
```

`w_k = e^{i phi_k}` with a lift `phi_1 < phi_2 < … < phi_n < phi_1 + 2 pi`,
`Phi = phi_1 + … + phi_n`, and `A_k` is the **open arc** from `w_k` to `w_{k+1}`
(indices cyclic, `A_n` running from `w_n` to `w_1 + 2 pi`).  Each `A_k` contains
no zero of `g`.  Put

```text
c = (-1)^{n+1} prod_k w_k,        q(z) = z^n - c,        |c| = 1.
```

> **Theorem C (concyclic alternation).**  There is an index `k` with
> ```text
> |g(z)| <= |q(z)|      for every z in A_k.                       (T1)
> ```

Three consequences, for that same `k`:

> **(T2)**  `max_{A_k} |g| <= 2`.  The constant `2` cannot be lowered: for
> `g = z^n - c` every one of the `n` arcs has maximum exactly `2`.
>
> **(T3)**  the arc `A_k` has angular width at most `2 pi / n`; equivalently
> `|w_{k+1} - w_k| <= 2 sin(pi/n)`.
>
> **(T4)**  `max_{[w_k, w_{k+1}]} |g| <= max_{A_k} |g|`, strictly for `n >= 3`
> (Lemma S below).  So the **chord** obeys the same bound as the arc.

Scaling to a circle of radius `rho` about `z_0` (`f(z) = rho^n g((z-z_0)/rho)`):

> **Theorem C′.**  Let `f` be monic of degree `n >= 2` with all zeros on a circle
> of radius `rho`.  Then two zeros `a, b`, adjacent along that circle, satisfy
> ```text
> |b - a| <= 2 rho sin(pi/n)     and     max_{[a,b]} |f| <= 2 rho^n,
> ```
> the second strictly for `n >= 3`.

> **Corollary C″ (Erdős #1041 for concyclic zeros of bounded radius).**
> If in addition `2 rho^n <= 1`, i.e. `rho <= 2^{-1/n}`, then two zeros of `f`
> are joined by a **straight segment** of length `<= 2 rho sin(pi/n) < 2` on
> which `|f| < 1`.  Erdős #1041 holds for every such `f`.
>
> Degree two needs no radius hypothesis: the chord between the two zeros has
> `|f| = |z-a||z-b| <= |a-b|^2/4 <= rho^2 < 1` and length `<= 2 rho < 2`.

The admissible radii are

| `n` | 3 | 4 | 5 | 6 | 8 | 10 | 20 |
|---|---|---|---|---|---|---|---|
| `2^{-1/n}` | 0.7937 | 0.8409 | 0.8706 | 0.8909 | 0.9170 | 0.9330 | 0.9659 |

Degrees two, three and four of Erdős #1041 are already settled unconditionally
(`exact_results::cubic_minimal_critical_value_short_hub`, and Pendyala's quartic),
so the **new** content of Corollary C″ begins at degree five.

## 2. Realification: why a circle admits alternation at all

For real `psi`,

```text
e^{i psi} - e^{i phi} = e^{i(psi+phi)/2} ( e^{i(psi-phi)/2} - e^{-i(psi-phi)/2} )
                      = e^{i(psi+phi)/2} · 2 i sin((psi-phi)/2),
```

so

```text
g(e^{i psi}) = i^n e^{i (n psi + Phi)/2} · G(psi),
      G(psi) = prod_{k=1}^n 2 sin((psi - phi_k)/2)   ∈  R.                (2.1)
```

Define, for any polynomial `p` of degree at most `n`, the **realification**

```text
R[p](psi) = (-i)^n e^{-i (n psi + Phi)/2} p(e^{i psi}).
```

By (2.1), `R[g] = G` is real, `|p(e^{i psi})| = |R[p](psi)|`, and `R[p](psi) = 0`
exactly when `p(e^{i psi}) = 0`.  Writing `p = sum_j b_j z^j` and
`beta_j = (-i)^n e^{-i Phi/2} b_j`,

```text
R[p](psi) = sum_{j=0}^n beta_j e^{i (j - n/2) psi},
```

which is real for all `psi` iff `beta_j = conj(beta_{n-j})` for every `j`.  Call
such a `p` **admissible**.  The admissible polynomials form a real vector space
of dimension `n+1`; `g` is admissible; and for an admissible `p`,

```text
b_n = 1   ==>   beta_n = (-i)^n e^{-i Phi/2}
              ==>   beta_0 = conj(beta_n)
              ==>   b_0 = (-1)^n prod_k w_k = g(0).                        (2.2)
```

**Every monic admissible polynomial has the same constant term as `g`.**  That
single fact is what makes the degree count in §3 work, and it is the exact
circle analogue of "two monic degree-`n` polynomials have a difference of degree
`<= n - 1`" in the collinear proof — here we get *two* matched coefficients, not
one.

`q(z) = z^n - c` is monic and admissible: `b_n = 1`, `b_0 = -c = (-1)^n prod w_k`
agrees with (2.2), and all middle coefficients vanish, so `beta_j = conj(beta_{n-j})`
holds trivially.  Explicitly

```text
R[q](psi) = beta_n e^{i n psi/2} + conj(beta_n) e^{-i n psi/2}
          = 2 cos( (n psi - Phi - n pi) / 2 ),                             (2.3)
```

so `|q(e^{i psi})| = |R[q](psi)| <= 2`, with equality on a set of `n` points per
period, and `R[q]` vanishes exactly at the `n` zeros of `q`, which are equally
spaced by `2 pi / n`.

Finally, from `sin(x + pi) = -sin x` and `e^{-i n (psi + 2 pi)/2} = (-1)^n e^{-i n psi/2}`,

```text
G(psi + 2 pi) = (-1)^n G(psi),        R[p](psi + 2 pi) = (-1)^n R[p](psi).  (2.4)
```

## 3. Proof of Theorem C

Let `H = R[g - q] = G - R[q]`, a real function, with `H(psi) = 0` exactly when
`(g-q)(e^{i psi}) = 0`, and `H(psi + 2 pi) = (-1)^n H(psi)` by (2.4).

Suppose (T1) fails for every `k`: for each `k` there is `psi_k` in the open arc
`A_k` with `|g(e^{i psi_k})| > |q(e^{i psi_k})|`, i.e.
`|G(psi_k)| > |R[q](psi_k)|`.  Choose the lift `phi_1 < psi_1 < phi_2 < psi_2 < …
< phi_n < psi_n < phi_1 + 2 pi` and set `psi_{n+1} = psi_1 + 2 pi`.

*Signs.*  `G` has a simple zero at each `phi_k` and no other zero, so `sign G`
alternates from arc to arc:  `sign G(psi_k) = eps · (-1)^k` for a fixed
`eps ∈ {±1}`.  Since `|G(psi_k)| > |R[q](psi_k)|`,

```text
sign H(psi_k) = sign G(psi_k) = eps (-1)^k,     k = 1, …, n,
```

and by (2.4), `sign H(psi_{n+1}) = (-1)^n sign H(psi_1) = eps (-1)^{n+1}`.  So
the `n+1` numbers `H(psi_1), …, H(psi_{n+1})` are nonzero and alternate in sign:
`H` has at least `n` zeros in the open interval `(psi_1, psi_1 + 2 pi)`, i.e.
`g - q` vanishes at at least `n` distinct points of the unit circle.

*Degree.*  `g` and `q` are both monic of degree `n` with the same constant term
by (2.2).  Hence `p := g - q` has `deg p <= n - 1` and `p(0) = 0`, so
`p(z) = z^m ptilde(z)` with `m >= 1` and `deg ptilde <= n - 1 - m <= n - 2`.  If
`p ≢ 0`, its nonzero roots number at most `n - 2`, so it has at most `n - 2`
zeros on the unit circle — contradicting the `n` just produced.  If `p ≡ 0` then
`g = q` and `|g(e^{i psi_1})| > |q(e^{i psi_1})|` is false.  Either way a
contradiction.  ∎

**(T2)** follows from (T1) and `|q| <= 2` on the circle.  Sharpness: for
`g = z^n - c` one has `c = (-1)^{n+1} prod w_k` (the product of the `n` roots of
`z^n = c` is `(-1)^{n+1} c`), so `q = g` and every arc has maximum exactly `2`;
hence `min_k max_{A_k} |g| = 2` there and no smaller constant is possible at any
degree.

**(T3)**  If the good arc `A_k` contained a zero `v` of `q`, then (T1) at `z = v`
gives `|g(v)| <= 0`, so `v` is a zero of `g` inside an open gap — impossible.  So
`A_k` avoids all `n` zeros of `q`, which are equally spaced by `2 pi / n`; an
open arc avoiding all of them has width at most `2 pi / n`.  Then
`|w_{k+1} - w_k| = 2 sin(delta_k / 2) <= 2 sin(pi/n)`.  ∎

## 4. Lemma S: the chord never beats its own arc

> **Lemma S.**  Let `n >= 2`, let `a, b` be zeros of `g` adjacent along the unit
> circle, `A` the open arc between them containing no other zero, and `S` the
> closed circular segment bounded by `A` and the chord `[a,b]`.  Then
> ```text
> max_{[a,b]} |g|  <=  max_{A} |g|,
> ```
> strictly when `n >= 3`.

*Proof.*  `u = log|g|` is harmonic on the open unit disk — every zero of `g` lies
on the boundary circle — continuous on `S \ {a,b}`, and `u -> -infinity` at `a`
and `b`.  Let `T = (b-a)/|b-a|` and let `N` be the unit normal to the chord
pointing from the chord into `S` (that is, towards `A`).

A chord of a circle separates its two arcs, so every zero `w_j` with
`w_j ∉ {a,b}` lies strictly on the far side of the line through `a, b`; that is,
`<z - w_j, N> > 0` for every `z` on that line.

For a unit direction `v` and `z_0` in the open chord,
`∂_v u(z_0) = Re( v · g'(z_0)/g(z_0) )` and `g'/g = sum_j 1/(z - w_j)`.  For
`j ∈ {a,b}` the vector `z_0 - w_j` is a real multiple of `T`, so `1/(z_0 - w_j)`
is a real multiple of `conj(T)` and `Re(N · lambda conj(T)) = lambda Re(N conj(T)) = 0`
because `N ⟂ T`.  For the other `j`, using `Re(N conj(zeta)) = <N, zeta>`,

```text
∂_N u(z_0) = sum_{j ∉ {a,b}}  <z_0 - w_j, N> / |z_0 - w_j|^2   >  0    (n >= 3).
```

So at **every** point of the open chord, `u` strictly increases into `S`.  Now
`max_S u` is attained; it is not attained in the interior of `S` (`u` is harmonic
and non-constant there), not at `a` or `b` (`u = -infinity`), and not at an
interior chord point (the displayed inequality produces nearby points of `S` with
larger `u`).  Hence it is attained on `A`, and `max_{[a,b]} u < max_A u`.

For `n = 2` the sum above is empty.  Compute directly with
`a = e^{-i delta/2}`, `b = e^{i delta/2}`: on the chord
`|g| = |z-a||z-b| <= |a-b|^2/4 = sin^2(delta/2)`, while at the midpoint `1` of the
arc `|g| = 4 sin^2(delta/4)`, and
`sin^2(delta/2) = 4 sin^2(delta/4) cos^2(delta/4) <= 4 sin^2(delta/4)`.  ∎

Lemma S is what turns Theorem C from a statement about an **arc** — whose length
`rho delta_k` carries no useful bound on its own — into a statement about a
**straight segment**, whose length is `2 rho sin(delta_k/2) <= 2 rho sin(pi/n) < 2`
for free.  This is the only place the length obligation of Erdős #1041 is
discharged, and it is discharged with room to spare.

## 5. What this does *not* do, and why

The equality family of Theorem C is `z^n - c`, i.e. the regular `n`-gon on the
circle — which is exactly the extremal family of Erdős #1041 recorded in
`negative_results` entries 17, 28 and 35 and in
[HardRegimeIsNearFekete.md](HardRegimeIsNearFekete.md).  So this route cannot
reach `rho -> 1`, and no sharpening of the *constant* will change that:

* the arc constant `2` is exactly optimal, because among monic admissible
  comparison polynomials `min max_{|z|=1} |q| = 2`.  Indeed `R[q]` has the form
  `2 cos(n psi/2 + theta) + (lower harmonics)`, and summing `R[q]` over the `n`
  points where the top harmonic equals `+2` kills every lower harmonic except
  the constant one, giving `sum = 2n + n c_0`; if `c_0 >= 0` some point has
  `R[q] >= 2`, and if `c_0 < 0` the `n` points where the top harmonic equals `-2`
  give some point with `R[q] <= -2`.
* on the regular `n`-gon the chord maximum is `rho^n (1 + cos^n(pi/n))`, which is
  `> rho^n` and tends to `2 rho^n`; and `1 + cos^n(pi/n) > 1` at every `n >= 2`.

So a chord — indeed any path that stays near the circle — is *provably* the wrong
object as `rho -> 1`.  On `z^n - rho^n` the components of `{|f| < 1}` are `n`
petals meeting only at the centre, and the unique shortest admissible path is the
pair of radii, of length exactly `2 rho`.  That is the cusp
`exact_results::near_fekete_cusp_law_and_strict_local_maximality` describes, and
this note does not touch it.

What the note does supply is the *other* half of that sandwich in an explicit,
unconditional, all-degree form: a concyclic configuration is handled by a plain
chord as soon as `rho <= 2^{-1/n}`.

## 6. Calibration

Receipts
`state/formal_math/erdos257_period_noncollapse/erdos1041_concyclic_alternation_receipt.json`
(verdict `PASS`) and
`state/formal_math/erdos257_period_noncollapse/erdos1041_concyclic_exact_witness.json`
(verdict `PASS`).  Verifiers
[scripts/check_erdos1041_concyclic_alternation.py](scripts/check_erdos1041_concyclic_alternation.py)
and
[scripts/check_erdos1041_concyclic_exact_witness.py](scripts/check_erdos1041_concyclic_exact_witness.py).

**Exact arm, no floats anywhere.**  Gaussian-rational zeros
`w(t) = ((1-t²) + 2ti)/(1+t²)` at `n = 4,5,6,7`, all arithmetic in `Fraction`:
`|w_k|² = 1`; the self-inversive coefficient identity `b_j = (-1)ⁿ W conj(b_{n-j})`
of §2 for `g` **and** for `q`; `q(0) = g(0)`; `(g-q)` has zero leading **and**
zero constant coefficient, so its nonzero-root count is `<= n-2` — that is the
entire degree half of §3, checked exactly.  Then `|g|² <= |q|² <= 4` at exact
points of a good arc, and after scaling to `rho = 4/5` the chord carries
`|f|² < 1` and squared length `< 4` at 41 exact rational parameters.

**Float arm.**  660 configurations at `n = 2 … 12` — random, near-regular with
perturbations `10⁻¹ … 10⁻⁶`, and two-cluster — with (T1)–(T4) checked on every
good gap: **0 failures**.

**Sharpness.**  At the regular `n`-gon every gap attains `max |g| = 2` to 15
digits and `min_k max_chord |g| = 1 + cosⁿ(π/n)` to 15 digits, `n = 2 … 10`; all
`n` gaps are good.

**Adversarial.**  Hill climbing on `min_k max_{A_k} |g|` reaches
`1.9999999999999998, 2.0, 1.9999999999999998, 1.9999999999999996, 2.0` at
`n = 3 … 7` — it saturates the budget and never crosses it.  The chord objective
reaches the regular-`n`-gon value to every printed digit at the same degrees.

**Negative control** (required by `negative_results` entry 19).  The same
searcher at the same budget must be able to push a neighbouring **false**
statement over the same threshold.  Against "*every* gap arc has `max |g| <= 2`"
it reaches `7.9999, 15.995, 31.951, 63.854, 127.30` at `n = 3 … 7` — i.e. it
finds configurations at essentially the absolute maximum `2ⁿ`.  The records above
are therefore not an artefact of a weak searcher.

**Deficit envelope.**  With `D = prod_{i<j}|w_i-w_j|² / nⁿ <= 1` the Fekete
deficit (`D = 1` exactly at the regular `n`-gon), climbing `min_k max_chord |g|`
inside `D`-bins gives a clean monotone envelope that crosses `1` at

| `n` | 3 | 4 | 5 | 6 | 7 |
|---|---|---|---|---|---|
| `D*` (envelope crosses 1) | ≈0.87 | ≈0.68 | ≈0.51 | ≈0.42 | ≈0.32 |

Below `D*` the plain chord already gives `max |f| < 1` at **every** radius
`rho < 1`, not only `rho <= 2^{-1/n}`.  See §8 for what this does and does not
buy.

## 6b. Two instrument defects found and fixed here

Both are recorded because `negative_results` entries 24, 34, 41 and 43–44 make
this a named class in this directory, and because the second is a **new**
member of it with the opposite sign.

* **Under-report, same sign as the recorded class.**  `|g(e^{iψ})|²` on the
  circle is `x^{-n} P(x)` for a degree-`2n` polynomial `P`, whose critical
  points solve `x P'(x) - n P(x) = 0`.  That polynomial is the right **locator**
  and the wrong **evaluator**: for clustered zeros it cancels catastrophically
  and returns values `10⁻⁸` relative below the truth, which flatters every
  containment statement scored on it.  Fix: locate with the polynomial, evaluate
  in the stable product form `prod_k |2 sin((ψ-φ_k)/2)|` in log space.  A second
  face of the same defect: the unit-circle root filter `| |x| - 1 | < 10⁻⁶`
  silently **drops** true circle roots at ill-conditioned configurations, and a
  dropped critical point can only lower a reported maximum.  Fix: `10⁻³` plus a
  dense grid safety net, never the locator alone.
* **Over-report — a new member of the class.**  On the wrapping gap
  `A_n = (φ_n, φ_1 + 2π)` a critical point selected by a test *modulo* `2π` is
  returned in `[0, 2π)`, hence can sit numerically *below* `a = φ_n`.  Feeding it
  unlifted to a bracketed local refinement inverts the bracket, and the
  refinement then reports values from **outside** the arc.  This manufactured 11
  false violations of (T2) in a 660-configuration sweep and an adversarial
  "record" of `25.2` against a budget of `2` — a refutation that was pure
  bookkeeping.  Fix: after any modular selection from a cyclic interval, **lift**
  into that interval's own branch, `ψ ← a + ((ψ - a) mod 2π)`, before any
  bracketed step.  General rule, since entries 24/34/41/44 are all under-report:
  a selection defect can point either way, so an apparent refutation deserves the
  same instrument audit as an apparent confirmation.  A brute-force cross-check
  against a `4·10⁵`-point sample on 400 configurations now returns `0`
  mismatches and worst good-gap arc maximum `1.894` against the budget `2`.

## 7. One conjecture, calibrated not proved

> **Conjecture (sharp chord constant).**  For `n` distinct points on the unit
> circle, `min_k max_{[w_k, w_{k+1}]} |g| <= 1 + cosⁿ(π/n)`, with equality
> exactly at the regular `n`-gon.

Adversarial hill climbing reaches the predicted value to every printed digit at
`n = 3,4,5,6,7` — `1.1249999999999998` against `1.125`, `1.25` against `1.25`,
`1.3465678107421708` against `1.346567810742171`, `1.421875` against `1.4218750`,
`1.4819128340102523` against `1.4819128340102523` — always from below and from
several seedings, while the same searcher breaks the neighbouring false statement
by two orders of magnitude.  Theorem C + Lemma S prove the weaker bound `2`.
Granting the conjecture moves the admissible radius in Corollary C″ from
`2^{-1/n}` to `(1 + cosⁿ(π/n))^{-1/n}` — `0.9615, 0.9457, 0.9424, 0.9435, 0.9459`
at `n = 3 … 7`, about `0.94` at every degree — but not to `1`, for the reason in
§5.

## 8. Producers this opens, and one that the data closes

* **P1 (adapted comparison) — priority 1.**  Theorem C holds for **every** monic
  admissible `q`, an `(n-1)`-real-parameter family, and only the uniform choice
  `q = z^n - c` has been spent.  Optimising `q` against the actual zero
  distribution is the exact circle analogue of scaling `T_n` to the root interval
  in [CollinearRootCase.md](CollinearRootCase.md).  It is the natural route both
  to the §7 conjecture and to a bound that stays useful when the zeros occupy a
  sub-arc (the near-collinear regime, where `2 rhoⁿ` is vacuous).  Do **not** try
  to lower the *uniform* arc constant: `min over the class of max_{|z|=1}|q|` is
  exactly `2`, proved in §5.
* **P2 (Lean).**  §2's realification, §2's coefficient matching, §3's sign count
  and §4's signed sum are finite algebra plus one intermediate-value argument.
  In range for a file next to
  [CollinearRootCase.lean](CollinearRootCase.lean).
* **P3 — the real target, and it is not the chord.**  For zeros on the unit
  circle the Form A-cut objective of
  [TruncatedSpokeReduction.md](TruncatedSpokeReduction.md) — truncated spokes
  plus a chord at a common radius `s` — is measured at `1` exactly on the regular
  `n`-gon (in the limit `s → 0`, where the path is the pair of radii of length
  exactly `2`) and strictly below `1` on every other concyclic configuration
  tested.  `V <= 1` for concyclic zeros would settle Erdős #1041 for **all**
  concyclic configurations at **every** radius `rho < 1`, since then
  `|f| = rhoⁿ |g| <= rhoⁿ < 1` on the path and the path has length `< 2 rho`.
  That is the concyclic case in one inequality.  Measured: adversarial climbing
  seeded on the regular `n`-gon at perturbation scales `10⁻¹ … 10⁻⁶` reaches
  `V = 1.000000000000` at `n = 3` and `0.999999999841`, `0.999999999787`,
  `0.999999997390` at `n = 4, 5, 6` — the maximum **is** the regular `n`-gon and
  `V` never crosses `1`;
  random configurations read `0.982, 0.854, 0.456, 0.554, 0.172, 0.239` at
  `n = 3 … 8`, so the constraint binds only in the near-regular shell.  Not a
  proof; `negative_results` entry 19 applies.  Degrees `7 … 10` are **not** on
  file — rerun
  [scripts/check_erdos1041_concyclic_form_a_cut.py](scripts/check_erdos1041_concyclic_form_a_cut.py)
  before quoting them.
* **CLOSED by the §6 envelope: the plain-chord deficit split.**  The obvious
  decomposition — "chord when the Fekete deficit `D` is small, near-Fekete cusp
  positivity when `D` is near one" — is a **bad** decomposition for the chord
  family, because the chord envelope crosses `1` at `D*` that *decreases* with
  degree (`0.87, 0.68, 0.51, 0.42, 0.32` at `n = 3 … 7`), while the cusp analysis
  is a leading-order expansion valid only as `D → 1`.  The middle band is not
  covered from either side, and it widens with `n`.  Any deficit split must use a
  path family that reaches `1` at the regular `n`-gon — that is P3, not the
  chord.  (This does not weaken Corollary C″, whose hypothesis is on the radius,
  not the deficit.)

## 9. Priority

No literature claim is made.  The realification
`g(e^{iψ}) = iⁿ e^{i(nψ+Φ)/2} G(ψ)` of a self-inversive polynomial is classical
Schur–Cohn material, and comparison with `z^n - c` is the obvious circle analogue
of Chebyshev comparison.  What this note asserts is the combination as an
alternation theorem on the gap arcs, the width bound (T3), Lemma S, and
Corollary C″.  A priority search has not been run.  The problem page records
Erdős #1041 as open with EHP58's connectedness result as the only stated prior
progress, and neither the degree-four paper nor the problem-page annex in
`annexes/` mentions collinear or concyclic zeros.
