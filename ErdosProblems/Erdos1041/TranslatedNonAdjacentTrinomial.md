# Erdős #1041 for arbitrarily translated non-adjacent trinomials

Status: ordinary analytic case theorem, assimilated 2026-09-05 from Type B
return batch `erdos1041_20260905_eight_return_stream_01`, source
`r07_centred_moments_translated_trinomials.md`.  Every proof step below was
re-derived in this pass.  No Lean formalisation exists yet.  This settles an
exact all-degree family and it does not settle unrestricted Erdős #1041.  No
literature-priority claim is made.

## Authority boundary

The universal quantifiers are carried by the ordinary analytic proofs recorded
here: the centroid moment localisation, the trinomial cancellation identity,
the root-count bound, the signed-defect bound, the balanced-weight duality, and
the coefficient envelope.  The sampling in
`scripts/check_erdos1041_translated_trinomial.py` is falsification evidence
only.  The section 8 quintic certificates in that script are exact rational
arithmetic.

The cancellation identity `(3.5)` is already corpus property; see
[CyclicTrinomialFiberCase.md](CyclicTrinomialFiberCase.md) §2 and
[AbelControlPolygon.lean](AbelControlPolygon.lean).  The new input is the
automatic selection of two roots at an arbitrarily translated hub.

## Theorem 1: the translated non-adjacent trinomial

Let

```text
f(z) = (z - h)^n + A (z - h)^m + C,   n >= 4,   1 <= m <= n - 2,
```

with `h, A, C` arbitrary complex numbers, and suppose every root lies in a
closed disc `D(q, R)`.  Put `H = |h - q|` and `sigma = sqrt(R^2 - H^2)`.  Then
two listed roots `a_i, a_j` are joined through `h` by two straight segments
with

```text
length([a_i, h] union [h, a_j]) <= 2 sigma,
|f(h + t (a_l - h))| <= sigma^n (1 - t^n),   0 <= t <= 1,   l in {i, j}.
```

If every root lies in the open unit disc, taking `q = 0` and
`R = max_k |a_k| < 1` gives `sigma <= R < 1`, so the connector has length below
`2` and stays inside `{|f| < 1}`.  Erdős #1041 holds for the family.  Repeated
listed roots permit the constant connector.

The hub `h` is not assumed to be the centre of the enclosing disc.  Individual
displacements `|a_k - h|` may exceed `R`, and even exceed `1`.  The proof
selects two for which they do not.

## Theorem 2: second- or third-moment localisation

Let `a_1, ..., a_n` lie in `D(q, R)`, let `h` be their centroid, put
`w_j = a_j - h` and `S_k = sum_j w_j^k`.  The centroid identity gives

```text
(1/n) sum_j |w_j|^2 = (1/n) sum_j |a_j - q|^2 - |h - q|^2 <= sigma^2,   (2.1)
```

so at least one displacement has modulus at most `sigma`.  For `n >= 4`, either
`S_2 = 0` or `S_3 = 0` forces at least two listed points with
`|a_j - h| <= sigma`.

Proof.  If `H = 0` then `sigma = R` and every point qualifies.  If `sigma = 0`
then `(2.1)` collapses every point onto `h`.  So assume `H > 0` and
`sigma > 0`.  Rotate by `theta = arg(h - q)`, writing
`e^(-i theta) w_j = x_j + i y_j` and `r_j = |w_j|`.  The enclosing-disc
condition becomes

```text
r_j^2 + 2 H x_j <= sigma^2.                                             (2.4)
```

Suppose exactly one displacement, relabelled `w_1`, has `r_1 <= sigma`.  Then
`x_j < 0` for `j >= 2`; put `t_j = -x_j > 0`, and centroid balance gives
`x_1 = sum_(j >= 2) t_j > 0`.

Second-moment case.  Real parts of the rotated identity `S_2 = 0` give
`sum_j r_j^2 = 2 sum_j x_j^2`.  Since
`sum_(j >= 2) t_j^2 <= (sum_(j >= 2) t_j)^2 = x_1^2`, the left side is at most
`4 x_1^2`.  It also exceeds `r_1^2 + (n-1) sigma^2 >= x_1^2 + (n-1) sigma^2`.
Hence `3 x_1^2 > (n-1) sigma^2`, which is impossible because
`x_1^2 <= r_1^2 <= sigma^2` and `n - 1 >= 3`.

Third-moment case.  From `Re (x + i y)^3 = 4 x^3 - 3 x (x^2 + y^2)`,

```text
Re(e^(-3 i theta) S_3)
  = 4 (x_1^3 - sum_(j >= 2) t_j^3)
  + 3 (sum_(j >= 2) t_j r_j^2 - x_1 r_1^2).                             (2.7)
```

The first bracket is non-negative because `sum_(j >= 2) t_j = x_1`.  The second
is strictly positive because `r_j^2 > sigma^2` for `j >= 2` while
`r_1^2 <= sigma^2`.  So the left side is positive, contradicting `S_3 = 0`.

The mechanism is that the enclosing disc pushes every escaping point into one
open half-plane, centroid balance makes the single remaining point carry all
the opposing first moment, and a vanishing second or third moment is
incompatible with that arrangement.

## Proof of Theorem 1

Put `P(w) = f(h + w) = w^n + A w^m + C`.  Because `m <= n - 2` the coefficient
of `w^(n-1)` vanishes, so `sum_j w_j = 0` and `h` is the centroid of the
original roots.

If `m <= n - 3`, the coefficients of `w^(n-1)` and `w^(n-2)` both vanish, so
`e_1 = e_2 = 0` and `S_2 = e_1^2 - 2 e_2 = 0`.

If `m = n - 2`, the coefficients of `w^(n-1)` and `w^(n-3)` vanish.  Here
`n >= 4` is used twice: it makes `n - 3 >= 1`, so that coefficient is not the
constant term, and it keeps the vanishing genuine.  Thus `e_1 = e_3 = 0` and
Newton's third identity `S_3 = e_1 S_2 - e_2 S_1 + 3 e_3` gives `S_3 = 0`.

Theorem 2 therefore supplies two roots `w_i, w_j` with modulus at most `sigma`.
Vieta and the arithmetic-geometric mean inequality give

```text
|C| = prod_k |w_k| <= ((1/n) sum_k |w_k|^2)^(n/2) <= sigma^n.            (3.4)
```

At a root, eliminating `A w^m` gives the exact cancellation identity

```text
P(t w) = (1 - t^m) C - (t^m - t^n) w^n.                                  (3.5)
```

Both scalar coefficients are non-negative on `[0,1]`, so for a selected root

```text
|P(t w)| <= (1 - t^m) |C| + (t^m - t^n) |w|^n <= sigma^n (1 - t^n).      (3.6)
```

The two arms have total length `|w_i| + |w_j| <= 2 sigma`.  No limiting or
genericity argument is used.

## Theorem 3: a larger safe star when the second moment vanishes

In the setting of Theorem 2, suppose `S_2 = 0` and `sigma > 0`, and let
`N_sigma` count the listed points with `|a_j - h| <= sigma`.  Then

```text
N_sigma > n (R + H) / (4 R + 2 H) >= n / 4,
N_sigma >= floor(n/4) + 1.
```

Proof.  Put `d = R - H` and `M = R + H`, so `sigma^2 = d M` and
`-M <= x_j <= d`.  For an outside point, `x_j < 0` and `x_j^2 <= -M x_j`, so
`2 x_j^2 - r_j^2 < -2 M x_j - sigma^2`.  Since `S_2 = 0` gives
`sum_j (2 x_j^2 - r_j^2) = 0` and `sum_j x_j = 0`, summation gives

```text
0 < sum_(j in I) (2 x_j^2 - r_j^2 + 2 M x_j) - (n - N) sigma^2.
```

For an inside point, `2 x_j^2 - r_j^2 + 2 M x_j <= x_j^2 + 2 M x_j`, and
`x^2 + 2 M x` is increasing on `[-M, d]`, so this is at most
`d^2 + 2 M d = d^2 + 2 sigma^2`.  Hence `0 < N (d^2 + 3 sigma^2) - n sigma^2`,
and `d^2 + 3 sigma^2 = (R - H)(4 R + 2 H)` finishes the count.  With no
outside points the conclusion is immediate.

For the family of Theorem 1 with `m <= n - 3`, at least `floor(n/4) + 1` listed
roots have their entire arms to `h` contained.  Under the open-unit-disc
hypothesis those arms form a connected star inside `{|f| < 1}`, and any two of
its vertices are joined through `h` with length at most `2 sigma < 2`.  This
part of the family supplies a controlled connected root cluster of that size.

## Theorem 4: a quantitative second-nearest-root bound

Order the centroid distances `r_(1) <= r_(2) <= ... <= r_(n)`.  For `H > 0` put
`M_2 = Re(e^(-2 i theta) S_2)`, `M_3 = Re(e^(-3 i theta) S_3)`, and

```text
D_0 = 2 H (R - H) / (n - 1),
D_2 = [3 (R - H)^2 - (n - 1) sigma^2 - M_2]_+ / (n - 1),
D_3 = sqrt(2 H (M_3)_+ / (3 (n - 1))).
```

Then for arbitrary `n >= 2`,

```text
r_(2)^2 <= sigma^2 + min{D_0, D_2, D_3}.
```

When `H = 0` use `r_(2) <= R` directly.

Proof.  Assume `delta = r_(2)^2 - sigma^2 > 0`, so exactly one point lies in the
centroid disc of radius `sigma`.  For `j >= 2`, `(2.4)` gives
`t_j >= delta / (2 H)`, hence `x_1 >= (n - 1) delta / (2 H)`, and
`x_1 <= R - H` proves `delta <= D_0`.  For the second moment,

```text
M_2 = 2 sum_j x_j^2 - sum_j r_j^2
    <= 4 x_1^2 - r_1^2 - (n - 1)(sigma^2 + delta)
    <= 3 (R - H)^2 - (n - 1)(sigma^2 + delta),
```

which rearranges to `delta <= D_2`.  For the third moment, `(2.7)` gives
`M_3 >= 3 x_1 delta`, so `M_3 >= 3 (n - 1) delta^2 / (2 H)` and
`delta <= D_3`.

Two exact sign conditions follow, both weaker than a vanishing moment:

```text
M_2 >= 3 (R - H)^2 - (n - 1) sigma^2   implies   r_(2) <= sigma,
M_3 <= 0                                implies   r_(2) <= sigma.
```

The geometry responds to the sign of the moment in the enclosing-disc
direction, and not merely to its size.

Maximising `sigma^2 + D_0` over `0 <= H <= R` at `H = R/(n+1)` gives the sharp
unconditional comparison

```text
r_(2) <= n R / sqrt(n^2 - 1).
```

For every odd `n >= 3` this is attained with `R = 1` by one point at `1` and
`(n-1)/2` copies of each of

```text
-1/(n^2 - 1) +- i sqrt(1 - 1/(n^2 - 1)^2).
```

Its centroid is `1/(n+1)`, and every non-exceptional centroid distance has
square `n^2/(n^2 - 1)`.  A second individual radius bound of `R` is therefore
unavailable from centroid balance alone.

## Theorem 5: the balanced-weight dual formula

Keep the centred displacements `w_j = a_j - h` and put

```text
rho_*^2 = inf_xi max_j (|w_j|^2 - 2 Re(conj(xi) w_j)).
```

Because the smallest disc centred at `h + xi` containing the roots has radius
`R_xi` with `R_xi^2 - |xi|^2 = max_j (|w_j|^2 - 2 Re(conj(xi) w_j))`, the
quantity `rho_*^2` is exactly the best value of `R^2 - |h - q|^2` obtainable
from enclosing discs.  Then

```text
rho_*^2 = max over p_j >= 0, sum_j p_j = 1, sum_j p_j w_j = 0
          of  sum_j p_j |w_j|^2,
```

and an optimal distribution can be supported on at most three root locations.

Proof.  For any balanced `p` and any `xi`, the balance condition gives
`sum_j p_j |w_j|^2 = sum_j p_j (|w_j|^2 - 2 Re(conj(xi) w_j))`, which is at
most the maximum.  For the reverse inequality, minimise the convex piecewise
affine function on the real span of the `w_j`.  A minimiser exists because the
uniform average of the `w_j` is zero, so the origin lies in the relative
interior of their convex hull.  At a minimiser the origin lies in the convex
hull of the active gradients `-2 w_j`, which supplies non-negative weights
summing to one with `sum_j p_j w_j = 0`.  All active affine functions share the
same value, so that value equals `sum_j p_j |w_j|^2`.  In the plane the
balancing representation reduces to at most three points by eliminating weights
along an affine dependence.

For the family of Theorem 1 this strengthens the conclusion to
`length <= 2 rho_*` with `|f| <= rho_*^n` on the connector.  The open-unit-disc
hypothesis gives `rho_* < 1`, because the original root-containing disc is an
admissible competitor.

## Theorem 6: a coefficient certificate with an open neighbourhood

Let a monic degree-`n` polynomial have roots in `D(q, R)` and expand about its
centroid,

```text
f(h + w) = w^n + sum_(k=1)^(n-2) b_k w^k + b_0,
```

the `w^(n-1)` coefficient vanishing by construction.  Choose `U` with
`r_(2) <= U`, taking `U^2 = sigma^2 + min{D_0, D_2, D_3}` when `H > 0` and
`U = R` when `H = 0`.  Then `|b_0| <= sigma^n <= U^n`.  Fix a pivot exponent
`m`.  Eliminating `b_m w^m` at a root gives

```text
f(h + t w) = (1 - t^m) b_0 + (t^n - t^m) w^n
           + sum_(k != m) b_k (t^k - t^m) w^k,
```

and each difference `t^k - t^m` has a fixed sign on `[0,1]`, so

```text
E_m(t; U) = (1 - t^m) |b_0| + (t^m - t^n) U^n
          + sum_(k != m) |b_k| U^k |t^k - t^m|
```

is a real polynomial envelope.  If `U < 1` and `max_[0,1] E_m(t; U) < 1` for
some pivot, then two roots are connected through the centroid by a curve of
length at most `2 U < 2` inside `{|f| < 1}`.

A simpler sufficient condition avoids the maximisation.  With

```text
d_km = max_[0,1] |t^k - t^m|
     = (|k-m|/max(k,m)) (min(k,m)/max(k,m))^(min(k,m)/|k-m|),
```

the budget

```text
U^n + sum_(k != m) |b_k| U^k d_km < 1
```

implies the hypothesis, including `U < 1`.

At a Theorem 1 polynomial with roots strictly inside the unit disc, every
coefficient in that sum vanishes when the trinomial exponent is the pivot, and
the left side is `sigma^n < 1`.  Small coefficient perturbations keep all roots
in a fixed disc of radius below one, and the centroid, centred coefficients and
moment bounds vary continuously, so the strict inequality persists.  The result
therefore covers a coefficient neighbourhood of every such instance that is
open and full-dimensional in coefficient space.

## The exact coprime quintic

Take `g(w) = w^5 - (461/525) w^3 - 64/525`, which factors as

```text
g(w) = (w - 1)(5 w + 4)(105 w^3 + 21 w^2 - 4 w + 16) / 525,
```

so `1` and `-4/5` are roots.  On `|w| = 3/4`,

```text
(461/525)(3/4)^3 - (3/4)^5 - 64/525 = 863/76800 > 0,
```

so by Rouché exactly three roots lie in `|w| < 3/4`.  All five lie in
`D(1/10, 9/10)`.  Put `s = 11/10` and `h = -11/100` and define

```text
F(z) = (z - h)^5 - (461/525) s^2 (z - h)^3 - (64/525) s^5,
```

whose roots are `z = s (w - 1/10)`, all with `|z| <= 99/100 < 1`.  The
exponents `5` and `3` are coprime, so no cyclic quotient exists, and `m = n-2`
places the instance in the third-moment branch.  One root has displacement
`11/10 > 1` from `h`, so any argument that needs every translated displacement
inside the unit disc is unavailable.

Theorem 1 applies with `R = 99/100`, `H = 11/100`, `sigma^2 = 121/125`, giving

```text
length(Gamma) <= 22 / (5 sqrt 5) = 1.9677398201... < 2,
max_Gamma |F| <= (121/125)^(5/2) = 0.9219097186... < 1.
```

Both are exact by rational squaring: `(2 sigma)^2 = 484/125 < 4` and
`sigma^2 = 121/125 < 1`.  These are uniform theorem bounds and not claims that
the selected connector is shortest.

## Sharpness at the closed level

For `f(z) = (z - q)^n - R^n` the hub is `h = q` and `sigma = R`.  If
`|w^n - R^n| <= R^n` with `w != 0` then `|w|^(2n) <= 2 R^n Re(w^n)`, so
`Re(w^n) > 0`.  That sublevel splits into `n` disjoint angular sectors holding
one root each, so any curve joining two roots inside the closed sublevel passes
through `w = 0` and has length at least `2 R`.  The two radial arms attain it
and satisfy `|f(q + t w)| = R^n (1 - t^n)`.  Both the length scale and the
spoke envelope are sharp at the closed level `sigma^n`.  Under the open-disc
hypothesis `R < 1`, so the strict Erdős conclusion is unaffected.

## What this adds over the corpus, exactly

[CyclicTrinomialFiberCase.md](CyclicTrinomialFiberCase.md) proves the centred
case `z^m + a z^r + c` for every exponent pair and every degree, and the
translated case `(z-h)^(q m) + a (z-h)^(q r) + c` for `q >= 2`, that is
exactly when `gcd` of the two positive exponents is at least two.  It records
translated coprime-exponent trinomials as its open boundary.

The family that is genuinely new here is therefore

```text
(z - h)^n + A (z - h)^m + C,   h != 0,   gcd(n, m) = 1,
n >= 4,   1 <= m <= n - 2.
```

Where the two overlap, `h = 0` or `gcd(n, m) >= 2`, the corpus result is
already strict and this note adds only the alternative envelope `sigma^n`.

Two boundaries stay open after this note.

- The translated adjacent family `(z - h)^n + A (z - h)^(n-1) + C`.  There `h`
  is generally not the centroid, and the Newton-moment step is absent.
- The translated coprime cubic `(z - h)^3 + A (z - h) + C`, since Theorem 2
  needs `n >= 4` in the second-moment branch and `m = n - 2 = 1` with `n = 3`
  puts the vanishing coefficient at the constant term.

## Consumers

- Closes the coprime translated boundary that
  [CyclicTrinomialFiberCase.md](CyclicTrinomialFiberCase.md) §4 records, for
  `m <= n - 2`.
- Theorem 4 supplies a metric radius `U` that
  [CentroidHubBudget.md](CentroidHubBudget.md) does not.  The corpus centroid
  facts give an interior hub and an ellipse membership, and Theorem 4 gives a
  second individual radius.
- Theorem 6 turns that radius into a finite coefficient test usable beyond
  trinomials.
- Theorem 5 replaces the ad hoc choice of enclosing disc by an attained
  optimum, giving `rho_*` in place of any particular `sigma`.

## Claim boundary

Nothing here establishes that an arbitrary monic polynomial satisfies a
containment certificate, and unrestricted Erdős #1041 remains open.  The
coefficient certificate does not overreach: applied to the exact quintic of
[CentroidHubCounterexample.md](CentroidHubCounterexample.md), where four of the
five centroid spokes provably leave the unit lemniscate, the simplified budgets
at pivots `1, 2, 3` are `1.16927981`, `1.05490983`, `1.06166219`, all above
one, so the certificate stays silent.  Two roots are localised there, and
visibility is proved only for the stated trinomial family.  No Lean module
exists for this note.

## Replay

```sh
./repo-python formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1041/scripts/check_erdos1041_translated_trinomial.py
```

The script emits one JSON line.  Its exact components are the section 8
factorisation, the Rouché margin `863/76800`, `sigma^2 = 121/125`, and the
bounds `(8.4)` and `(8.5)` by rational squaring.  Its sampled components are
the moment localisation and spoke envelope over translated trinomials of
degrees `4` to `14` with every `m <= n - 2`, the star count, the Theorem 4
bound with its sharp configuration, the balanced-weight duality against exact
linear-programme vertices, and the non-firing of the coefficient certificate on
the stored centroid-hub counterexample.  The sampled components are
falsification evidence and carry no universal authority; the centroid-hub
budgets are float diagnostics computed over an exact rational configuration.
