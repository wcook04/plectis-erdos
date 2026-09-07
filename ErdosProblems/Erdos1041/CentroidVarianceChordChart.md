# Erdős #1041: the centroid-variance chord chart, and why variance cannot reach the critical spectrum

Status: two ordinary analytic theorems and one exactly certified all-degree
refutation, 2026-09-05. No Lean formalisation exists yet. This settles a
root-statistic regime of Erdős #1041 and it does not settle the unrestricted
problem. No literature-priority claim is made.

## Authority boundary

The universal quantifiers are carried by the ordinary proofs below: the
mean-square envelope, the pair-selection Markov step and its sharp
configuration, the Cauchy--Schwarz/AM--GM comparison with the corpus carrier
optimum, and the integer inequality of section 4. The certificate of section 4
is exact rational arithmetic. Everything in section 5 is measurement and is
falsification evidence only.

The mean-square envelope of section 1 is **already corpus property**: it is the
uniform-weight member `p_j = 1/n` of the disc envelope `(A)`/`(B)` in
[BarycentricEnvelope.md](BarycentricEnvelope.md). The chord functional `Phi` of
section 3 is likewise corpus property: it is the `p = 1` minimax value
`(Bdual)` of the same note, which computes it for an arbitrary point pair and
uses it there for a no-go at the regular quartic. What is new here is the
root-pair selection, the exact variance threshold with its extremal family, and
the refutation in section 4.

## Setting

Throughout, `a_1, ..., a_n` are complex numbers with `n >= 2`,
`f(z) = prod_k (z - a_k)`, and

```text
c   = (a_1 + ... + a_n)/n,          d_k  = |a_k - c|,
Var = (1/n) sum_k d_k^2,            r_(1) <= r_(2) <= ... <= r_(n)
```

is the increasing rearrangement of the `d_k`. `Var` is the second central
moment of the root multiset; it is translation invariant and scales like a
squared length. If every root lies in the open unit disc then `Var < 1`.

The centroid identity used throughout is, for every complex `z`,

```text
sum_k |z - a_k|^2 = n (|z - c|^2 + Var),                                 (0.1)
```

which follows by expanding `|(z - c) - (a_k - c)|^2` and using
`sum_k (a_k - c) = 0`. Its specialisation at a root is
`sum_k |a_i - a_k|^2 = n (d_i^2 + Var)`.

## 1. The mean-square envelope

> **Proposition 1.** For every `z`,
> `|f(z)|^(2/n) <= |z - c|^2 + Var`.
> Consequently the open disc `D(c, sqrt(1 - Var))` lies in `{|f| < 1}` whenever
> `Var < 1`.

*Proof.* AM--GM on the `n` nonnegative numbers `|z - a_k|^2` gives
`|f(z)|^(2/n) = (prod_k |z-a_k|^2)^(1/n) <= (1/n) sum_k |z-a_k|^2`, and the
centroid identity applied at `z` turns the right side into `|z-c|^2 + Var`. ∎

This is `(B)` of [BarycentricEnvelope.md](BarycentricEnvelope.md) at the
uniform weight vector, where `G(p) = 1/n`, `h(p) = c`, `V(p) = Var`, and the
carrier radius is `sqrt(T^(2/n) - Var)`.

The centre is not a free parameter. The bound
`|f(z)|^(2/n) <= (1/n) sum_k |z - a_k|^2` holds at every `z`, and the right side
is the paraboloid `|z - c|^2 + Var`, so the largest disc it certifies is
centred at the centroid and has radius exactly `sqrt(1 - Var)`. Re-centring the
same uniform bound at any other point strictly shrinks it. Improvement requires
leaving the uniform weights, which is what section 3 does.

## 2. The chord chart and its sharp variance threshold

> **Theorem 2.** If two distinct roots `a_i != a_j` satisfy
>
> ```text
> max(d_i, d_j)^2 + Var < 1,                                            (2.1)
> ```
>
> then the closed segment `[a_i, a_j]` lies in `{|f| < 1}`. If in addition every
> root lies in the open unit disc, that segment is a curve of length
> `|a_i - a_j| <= |a_i| + |a_j| < 2` joining two distinct roots inside
> `{|f| < 1}`, so Erdős #1041 holds for `f`.

*Proof.* `|z - c|^2` is convex, so on the segment it is at most its larger
endpoint value `max(d_i, d_j)^2`. Proposition 1 then gives
`|f(z)|^(2/n) <= max(d_i,d_j)^2 + Var < 1` at every point of the segment. The
length statement is the triangle inequality in the open unit disc. ∎

Condition `(2.1)` is exactly the statement that both roots lie in the open disc
of Proposition 1. Because the condition is monotone in `max(d_i, d_j)`, the
optimal choice of pair is the two centroid-nearest roots, and `(2.1)` becomes

```text
r_(2)^2 + Var < 1.                                                      (2.2)
```

> **Corollary 3 (variance-only threshold).** If
>
> ```text
> Var < (n-1)/(2n-1),                                                   (2.3)
> ```
>
> then `(2.2)` holds. Hence every monic `f` of degree `n >= 2` with distinct
> roots in the open unit disc and second central moment below `(n-1)/(2n-1)`
> satisfies Erdős #1041 by a straight root chord.

*Proof.* Suppose `(2.2)` fails, so `r_(2)^2 >= 1 - Var`. Then the `n-1`
distances `r_(2), ..., r_(n)` all have squares at least `1 - Var`, and

```text
n Var = sum_k d_k^2 >= r_(1)^2 + (n-1)(1 - Var) >= (n-1)(1 - Var),
```

which rearranges to `(2n-1) Var >= n-1`. ∎

The threshold rises from `1/3` at `n = 2` to `1/2` as `n -> infinity`. For
`n >= 3` the Markov step is sharp, and its equality case is an admissible
configuration: take `rho^2 = n/(2n-1)` and

```text
f(z) = z^n - rho^(n-1) z   translated to any centre,
```

that is, one root at the centroid and `n-1` roots forming a regular
`(n-1)`-gon of radius `rho`. Then `c = 0`, `Var = (n-1) rho^2 / n =
(n-1)/(2n-1)`, `1 - Var = rho^2`, and `r_(2) = rho`, so `(2.2)` holds with
equality and `(2.3)` fails with equality. Every root has modulus at most
`rho < 1`, so the configuration is admissible. The refinement of the same step,

```text
Var < ((n-1) + r_(1)^2) / (2n-1)   implies (2.2),                       (2.4)
```

is immediate from the displayed chain and is the exact form of the deduction.

Erdős #1041 is not in doubt at that boundary configuration: the segment from
the central root to any outer root has length `rho < 1` and satisfies
`|f| = rho^n t (1 - t^(n-1)) < 1` along it. The sharpness is a statement about
the sufficient condition, not about the problem.

## 3. Where the chart sits in the corpus carrier lattice

For a pair `i != j` put

```text
Phi_ij(t) = prod_k ( t |a_i - a_k| + (1-t) |a_j - a_k| ),   0 <= t <= 1.
```

> **Theorem 4.** If `max_[0,1] Phi_ij < 1` then `[a_i, a_j] subset {|f| < 1}`.
> Moreover `(2.1)` implies `max_[0,1] Phi_ij < 1`, so Theorem 4 covers every
> configuration Theorem 2 covers and strictly more.

*Proof.* For `z = t a_i + (1-t) a_j` the triangle inequality gives
`|z - a_k| <= t|a_i-a_k| + (1-t)|a_j-a_k|` for every `k`; multiplying over `k`
gives `|f(z)| <= Phi_ij(t)`. For the comparison, Cauchy--Schwarz on each factor
gives `Phi_ij(t)^2 <= prod_k c_k(t)` with
`c_k(t) = t|a_i-a_k|^2 + (1-t)|a_j-a_k|^2`, and AM--GM with `(0.1)` gives

```text
(prod_k c_k(t))^(1/n) <= (1/n) sum_k c_k(t)
                       = t(d_i^2 + Var) + (1-t)(d_j^2 + Var)
                       <= max(d_i,d_j)^2 + Var.
```

So `Phi_ij(t)^(2/n) <= max(d_i,d_j)^2 + Var < 1`. Strictness of the inclusion
is inherited. ∎

By `(Bdual)` of [BarycentricEnvelope.md](BarycentricEnvelope.md),
`max_t Phi_ij(t)` is exactly `(M(a_i,a_j)/n)^n`, the optimal value over the
whole fixed-weight `p = 1` carrier family for that pair. Theorem 4 is therefore
the *best* criterion the corpus carrier lattice can give for a straight root
chord, and Theorem 2 is its variance-explicit weakening. The strictness is real:
on random configurations of degrees 3 to 8 the `Phi` criterion fires on every
sample while `(2.2)` fires on 81.6 to 96.3 per cent of them (section 5).

## 4. Variance cannot reach the critical spectrum: an exact refutation

`HardRegimeIsNearFekete.md` records `mu^(n-1) <= D <= 1` with
`D = prod_(i<j)|a_i-a_j|^2 / n^n` and `mu` the least critical-value modulus.
Composing the chart of section 2 with
[LowCriticalPotentialClosure.md](LowCriticalPotentialClosure.md) needs a bridge
from `Var` to `mu`. The natural candidate is forced by dimensional analysis
together with sharpness on the extremal family: both sides of each of

```text
D  <=  Var^(n(n-1)/2),                                                  (4.1)
mu <=  Var^(n/2),                                                       (4.2)
```

are invariant under translation and have the same homogeneity, and both hold
with equality on the extremal family `z^n - r^n`, where `Var = r^2`,
`D = r^(n(n-1))` and `mu = r^n`. Statement `(4.1)` says the regular `n`-gon
maximises the discriminant at fixed second moment; `(4.2)` is what a variance
chart would need in order to hand the complementary regime to the low-critical
closure.

> **Theorem 5.** Both `(4.1)` and `(4.2)` are false for every `n >= 6`.
> The single family
>
> ```text
> f_n(z) = z^n - z          (roots: 0 and the (n-1)-st roots of unity)
> ```
>
> refutes both, and after the scaling `z -> s z` with any `0 < s < 1` every root
> lies in the open unit disc while both ratios are unchanged. Explicitly
>
> ```text
> Var = (n-1)/n,     D = mu^(n-1) = (n-1)^(n-1)/n^n,
> mu  = (n-1) / n^(n/(n-1)),
> D / Var^(n(n-1)/2) = (mu / Var^(n/2))^(n-1)
>                    = n^(n(n-3)/2) / (n-1)^((n-1)(n-2)/2)  >  1.       (4.3)
> ```
>
> At `n = 6` the certificate is the integer inequality
> `6^9 = 10077696 > 9765625 = 5^10`, a ratio of `1.03195...`, with
> `mu / Var^3 = 1.00631...`. Since `mu / Var^(n/2) -> sqrt(e) = 1.6487...`, the
> ratio in `(4.3)` is unbounded. Over the computed range `6 <= n <= 40` both
> ratios increase with `n`; only the limit is proved here.

*Proof.* The roots of `f_n` are `0` and the `(n-1)`-st roots of unity, so the
centroid is `0` and `n Var = n - 1`. The discriminant splits into the `n-1`
centre-to-vertex pairs, contributing `1` each, and the discriminant of the
regular `(n-1)`-gon of radius one, which is `(n-1)^(n-1)`; hence
`prod_(i<j)|a_i-a_j|^2 = (n-1)^(n-1)` and `D = (n-1)^(n-1)/n^n`. Since
`f_n'(z) = n z^(n-1) - 1`, every critical point has `|z| = n^(-1/(n-1))` and
`f_n(z) = z(z^(n-1) - 1) = z(1/n - 1)`, so all `n-1` critical values share the
modulus `mu = (n-1) n^(-n/(n-1))` and `mu^(n-1) = (n-1)^(n-1)/n^n = D`. Then

```text
D / Var^(n(n-1)/2) = ((n-1)^(n-1)/n^n) * (n/(n-1))^(n(n-1)/2)
                   = n^(n(n-1)/2 - n) / (n-1)^(n(n-1)/2 - (n-1))
                   = n^(n(n-3)/2) / (n-1)^((n-1)(n-2)/2),
```

using `n(n-1)/2 - n = n(n-3)/2` and `n(n-1)/2 - (n-1) = (n-1)(n-2)/2`. Write
`B = (n-1)(n-2)/2`, so the exponent of `n` is `B - 1` and the logarithm of the
ratio is

```text
phi(n) = B log(n/(n-1)) - log n.
```

From `-log(1-x) > x + x^2/2` on `(0,1)` with `x = 1/n`,

```text
phi(n) > B/n + B/(2n^2) - log n
       = (n/2 - 3/2 + 1/n) + (n-1)(n-2)/(4n^2) - log n.
```

The function `n/2 - 3/2 - log n` is increasing for `n > 2` and equals
`-0.29180...` at `n = 6`, while the two remaining terms are at least
`1/6 + 20/144 = 0.30555...` there and both are positive for all `n >= 6`.
Hence `phi(n) > 0` for every `n >= 6`. Since `mu^(n-1) = D` for this family,
`(4.2)` fails exactly when `(4.1)` does. The limit
`mu/Var^(n/2) = (n-1)^(1-n/2) n^(n/2 - n/(n-1)) -> e^(1/2)` follows from
`(n/2) log(n/(n-1)) -> 1/2` and `log(n-1) - (n/(n-1)) log n -> 0`. ∎

`f_n` is a binomial, hence already covered as an instance of the trinomial
families of [CyclicTrinomialFiberCase.md](CyclicTrinomialFiberCase.md) and
[TranslatedNonAdjacentTrinomial.md](TranslatedNonAdjacentTrinomial.md); no
counterexample to Erdős #1041 is claimed or implied. What dies is the bridge.
The corollary for the two-chart programme is exact: **`Var` alone cannot bound
`mu`**, so a composed cover of the form (variance chart) + (low-critical
closure) needs a third invariant, and the same computation shows that the
`n`-gon-maximises-the-discriminant intuition, correct for the maximum-modulus
normalisation via Fekete, is false for the second-moment normalisation from
`n = 6` on. The failing configuration is not exotic: it is one root at the
centroid surrounded by a regular `(n-1)`-gon, which is exactly the equality
case of Corollary 3.

## 5. Measurement: the chart landscape

Falsification evidence only; no universal claim is made from this section.

On the regular `n`-gon of radius `r` we have `c = 0`, `Var = r^2` and
`r_(2) = r`, so condition `(2.2)` reads exactly `2 r^2 < 1`: the variance chart
has critical radius `1/sqrt 2` at every degree, and that row of the table below
is a theorem rather than a measurement. Measured critical radii, by bisection to
`2^-45`:

| n | `(2.2)` | `Phi` (Thm 4) | direct chord | `mu <= 197/1000` |
|---|---|---|---|---|
| 3 | 0.70711 | 0.91649 | 0.96150 | 0.58186 |
| 4 | 0.70711 | 0.91018 | > 0.999999 | 0.66622 |
| 5 | 0.70711 | 0.91535 | 0.99775 | 0.72259 |
| 6 | 0.70711 | 0.92233 | > 0.999999 | 0.76280 |
| 7 | 0.70711 | 0.92902 | 0.99975 | 0.79288 |
| 8 | 0.70711 | 0.93497 | > 0.999999 | 0.81622 |
| 10 | 0.70711 | 0.94466 | > 0.999999 | 0.85005 |
| 12 | 0.70711 | 0.95202 | > 0.999999 | 0.87338 |

The `n = 3` chord entry is exact as well.

> **Lemma 6.** For `f(z) = z^3 - r^3` and any two distinct roots, the maximum of
> `|f|` on their chord is `(9/8) r^3`, attained only at the midpoint. Hence that
> chord lies in `{|f| < 1}` if and only if `r^3 < 8/9`, and the critical radius
> is `(8/9)^(1/3) = 0.9614997135...`, at which `Var = (8/9)^(2/3) =
> 0.9244988...`.

*Proof.* Scale by `r` and put `u = 1 + t(omega - 1)` with `omega = e^(2 pi i/3)`,
so `|f| = r^3 |u^3 - 1|` on the chord. With `s = t - 1/2` and `m = 3 s^2`,
`|u|^2 = m + 1/4`, and writing `u = x + iy` one computes `x^2 - 3y^2 = -1/2 - 3s`
and `x = 1/4 - 3s/2`, so `Re(u^3) = x(x^2 - 3y^2) = -1/8 + 9 s^2/2`. Hence

```text
|u^3 - 1|^2 = |u|^6 - 2 Re(u^3) + 1 = m^3 + (3/4) m^2 - (45/16) m + 81/64.
```

Its derivative `3m^2 + (3/2)m - 45/16` has its positive root at `m = 3/4`, so the
cubic decreases on `[0, 3/4]`, which is exactly the range of `m` for
`t in [0,1]`. The maximum is at `m = 0`, that is `t = 1/2`, with value
`81/64`. ∎

The `> 0.999999` entries at even `n` are exact: for even `n` the diameter chord
`[-r, r]` of `z^n - r^n` satisfies `|f| = r^n - z^n` there, which lies in
`[0, r^n] subset [0,1)`. So the extremal family is joined by a straight root
chord at every even degree and every `r < 1`, and only the odd degrees, `n = 3`
most severely, force the origin hub. Negative result 16 of the kill-list, the
cubic `z^3 - (99/100)^3` with every root-pair midpoint outside `{|f| < 1}`, is
the `n = 3` row of this table and is not typical of the family.

Coverage on 1200 configurations per degree drawn with `sqrt`-uniform radius in
`|z| < 0.999` and uniform angle:

| n | `(2.2)` fires | `Phi` fires | some chord contained |
|---|---|---|---|
| 3 | 979/1200 | 1200/1200 | 1200/1200 |
| 4 | 1045/1200 | 1200/1200 | 1200/1200 |
| 5 | 1087/1200 | 1200/1200 | 1200/1200 |
| 6 | 1107/1200 | 1200/1200 | 1200/1200 |
| 7 | 1137/1200 | 1200/1200 | 1200/1200 |
| 8 | 1155/1200 | 1200/1200 | 1200/1200 |

Under near-Fekete seeding (angles and radii perturbed from the regular `n`-gon
at radius `0.999` by `10^-4` to `10^-1`), 400 configurations per degree:

| n | `(2.2)` | `Phi` | some chord contained |
|---|---|---|---|
| 3 | 0/400 | 15/400 | 45/400 |
| 4 | 0/400 | 16/400 | 400/400 |
| 5 | 0/400 | 19/400 | 244/400 |
| 6 | 0/400 | 27/400 | 400/400 |
| 7 | 0/400 | 39/400 | 400/400 |
| 8 | 0/400 | 49/400 | 400/400 |

Both tables describe *seeded* samples, and neither locates the chordless region.
A direct adversarial maximisation of

```text
J(a) = min over pairs of  max_{[a_i,a_j]} |f|,      J > 1 <=> chordless,
```

does locate it, and it is **not** confined to odd degree:

| n | `sup J` found | `D` there | `Var` | `max|a_k|` | least pair distance |
|---|---|---|---|---|---|
| 4 | 1.03032 | 0.94809 | 0.99607 | `1 - 10^-6` | 1.25208 |
| 6 | 1.03613 | 0.92599 | 0.99921 | `1 - 10^-6` | 0.83892 |

The near-Fekete-seeded census above found nothing at `n = 4` and `n = 6` only
because it never entered that basin. This is negative result 28 of the kill-list
applying to this lab: a seeded census records its basin, not the truth. What the
two censuses do support is a statement about *density* rather than emptiness —
under the sampling described, chordless configurations are rare at even degree
and common at `n = 3`.

Minimising `Var` subject to `J > 1` measures the exact gap left by Corollary 3
in its own coordinate:

| n | proved threshold `(n-1)/(2n-1)` | measured chordless variance floor |
|---|---|---|
| 3 | 0.40000 | 0.9244988 |
| 5 | 0.44444 | 0.9793279 |
| 7 | 0.46154 | 0.9867569 |

At `n = 3` the floor is exactly `(8/9)^(2/3) = 0.92449883...` by Lemma 6, and it
is attained at the regular triangle: the search reproduces the closed form to
seven digits. So Corollary 3 is not close to the truth in the variance
coordinate, and the whole interval `Var in [(n-1)/(2n-1), V_n)` is lost to the
Markov step rather than to the geometry.

The Fekete ratios of the located chordless configurations are `0.79` (`n = 3`),
`0.95` (`n = 4`), `0.67` (`n = 5`), `0.93` (`n = 6`) and `0.84` (`n = 7`). These
are within a bounded factor of the Fekete maximum — a generic random
configuration of degree 6 has `D` near `6 * 10^-6` — but they are not
asymptotically at it, unlike the hub-obstruction witnesses of
[HardRegimeIsNearFekete.md](HardRegimeIsNearFekete.md), which have
`D > 0.99994`. So the chord obstruction and the hub obstruction do not live at
the same distance from the Fekete maximiser, and "near-Fekete" is too coarse a
description of the chordless region.

## Claim boundary

Sections 1 to 3 prove a sufficient condition and a regime; they do not prove
unrestricted Erdős #1041, and Corollary 3's threshold provably cannot be raised
by the Markov step alone. Section 4 refutes two bridge inequalities; it makes no
statement about Erdős #1041 and exhibits no counterexample to it. Section 5 is
measurement over finitely many configurations at finite precision and carries no
universal authority; the two exact statements inside it (the `1/sqrt 2` critical
radius and the even-degree diameter chord) are proved above and in the table
caption. No Lean module exists for this note.

## Consumers

- [BarycentricEnvelope.md](BarycentricEnvelope.md): Theorem 4 records that the
  `p = 1` minimax `(Bdual)`, used there for an attachment no-go at an
  origin/root pair, is a *positive* criterion at a root/root pair, and section 5
  measures how far it reaches.
- [CentroidHubBudget.md](CentroidHubBudget.md): that note gives the centroid an
  interior hub and an ellipse membership but leaves visibility open, and
  [CentroidHubCounterexample.md](CentroidHubCounterexample.md) retires universal
  centroid visibility. Theorem 2 gives the complementary positive statement:
  centroid *proximity* of two roots, measured against `sqrt(1 - Var)`, forces the
  chord rather than the spokes.
- [TranslatedNonAdjacentTrinomial.md](TranslatedNonAdjacentTrinomial.md):
  Theorem 4 there bounds `r_(2)` by enclosing-disc data; Corollary 3 here bounds
  the same quantity by second-moment data, and section 4 shows the second moment
  cannot be pushed further into the critical spectrum.
- [HardRegimeIsNearFekete.md](HardRegimeIsNearFekete.md): section 4 answers the
  second-moment version of its stability question in the negative, and section 5
  measures that the chordless region sits at Fekete ratio `0.67` to `0.95`,
  four to five orders of magnitude further from the maximiser than its own
  hub-obstruction witnesses.

## Replay

```sh
./repo-python formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1041/scripts/check_erdos1041_centroid_variance_chord_chart.py
```

The script emits one JSON line. Its exact components are the section 4
certificate for `6 <= n <= 40` in integer arithmetic together with the exact
rational values of `Var`, `D` and `mu^(n-1)` for `f_n`, the exact rational
verification of the Corollary 3 sharp configuration, and the exact rational
even-degree diameter-chord statement. Its sampled components are the
Proposition 1 envelope, the Theorem 2 implication, the Theorem 4 implication and
hierarchy, and the Corollary 3 threshold, over random configurations; those are
falsification evidence and carry no universal authority.
