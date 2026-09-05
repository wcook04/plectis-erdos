# Erdős #1041 for quadrinomials whose roots lie on one centred circle

Status: ordinary analytic case theorem, assimilated 2026-09-05 from Type B
return batch `erdos1041_20260905_eight_return_stream_01`, source
`r03_centred_circle_quadrinomials.md`.  Every proof step below was re-derived
in this pass.  No Lean formalisation exists yet.  This settles an exact
all-degree family and it does not settle unrestricted Erdős #1041.  No
literature-priority claim is made.

## Authority boundary

The universal quantifiers are carried by the ordinary analytic proofs recorded
here: the exact radial identity `(9)`, the phase-crossing count, the
Newton/Gram amplitude bounds, the semicircle lemma with its arc estimate, and
the Schur maximum-principle argument.  The sampling in
`scripts/check_erdos1041_centred_circle_quadrinomial.py` is falsification
evidence only.  The rational certificates in that script are exact.

The composed inequality `(50)` consumes the corpus result
[FreePointQuadraticAllDegrees.md](FreePointQuadraticAllDegrees.md), which is
itself an ordinary proof and not Lean-checked.  Nothing here upgrades that
status.

## Theorem 1: the paired quadrinomial connector

Let

```text
p(z) = z^n + omega conj(a) z^(n-k) + a z^k + omega,
|omega| = 1,   1 <= k < n/2,   n >= 4,
```

and suppose all `n` roots of `p`, with multiplicity, lie on `|z| = 1`.  Then
two root occurrences are joined by a curve of length at most `2` inside
`{|p| <= 1}`.  When the roots are distinct, one of two certificates holds.

Radial certificate.  Two distinct roots `zeta_1, zeta_2` satisfy

```text
|omega + a zeta^k| <= 1,
```

and then `|p(t zeta)| <= 1 - t^n` for `0 <= t <= 1`, so the broken line
`zeta_1 -> 0 -> zeta_2` is contained and has length `2`.

Circular-arc certificate.  The parameters satisfy `n = 3k` and `|a| > sqrt(3)`,
and two roots are joined by a unit-circle arc `gamma` with

```text
length(gamma) < 2 pi / (5 k),      sup_gamma |p| < 3 - sqrt(5) < 1.
```

The two branches are not exclusive.  They exhaust the class.

Strictification.  For `0 < r < 1` put `f_r(z) = r^n p(z/r)`.  Its roots all
have modulus `r`, the scaled connector has length at most `2 r < 2`, and
`|f_r| <= r^n < 1` on it.  So `f_r` satisfies the strict Erdős #1041
conclusion.

### Corollary: monic polynomials with at most four non-zero coefficients

Let `f` be monic of degree `n >= 4` with at most four non-zero coefficients and
every root of modulus `r`, `0 < r < 1`.  Then `f` satisfies Erdős #1041.

Normalising by `p(z) = r^(-n) f(r z)` puts every root on the unit circle.  A
monic polynomial with unimodular roots satisfies `p_j = omega conj(p_(n-j))`
with `omega = p(0)`, so the involution `j -> n - j` preserves the support.
With exactly four non-zero coefficients the two intermediate exponents form a
pair `k, n-k`, which is the displayed form.  With at most three coefficients
the corpus centred-trinomial theorem
[CyclicTrinomialFiberCase.md](CyclicTrinomialFiberCase.md) already applies.

The common-circle hypothesis is load-bearing.  This is not a statement about
unrestricted Schur-stable quadrinomials.

## Proof

### The radial identity

At a root `zeta` put `S = omega + a zeta^k`.  The root equation gives
`omega conj(a) zeta^(n-k) = -S - zeta^n`, and substitution yields the exact
identity

```text
p(t zeta) = (1 - t^k) omega + (t^k - t^(n-k)) S - (t^(n-k) - t^n) zeta^n.  (9)
```

On `[0,1]` the three weights are non-negative because `k <= n - k`, and they
sum to `1 - t^n`.  Since `|omega| = |zeta^n| = 1`, the condition `|S| <= 1`
gives `|p(t zeta)| <= 1 - t^n`.  With `d = 1 - |S|` the sharper form is
`|p(t zeta)| <= 1 - t^n - d (t^k - t^(n-k))`.

This is the four-term instance of the corpus Abel control polygon
[AbelControlPolygon.lean](AbelControlPolygon.lean).  The new content is the
existence of two admissible roots, and the arc construction where no such pair
need exist.

### The phase representation

Write `A = |a|` and `u(theta) = (a/omega) e^(i k theta)`.  Dividing the root
equation by `omega` gives `(zeta^n/omega)(1 + conj(u)) + (1 + u) = 0`, so for
`A != 1`

```text
p(e^(i theta)) = 0   iff   Psi(theta) = arg(-omega)  mod 2 pi,
Psi(theta) = n theta - 2 arg(1 + u(theta)),
Psi'(theta) = n - 2 k Re(u/(1+u)).                                       (16)
```

Radial admissibility is `|1 + u| <= 1`, that is `Re u <= -A^2/2`, because
`S = omega (1 + u)`.

### Small amplitude, `0 < A < 1`

Put `h = arcsin(A/2)`, so `0 < h < pi/6`.  The good set is
`arg u` in `[pi/2 + h, 3 pi/2 - h]`, giving `k` disjoint theta-arcs of length
`(pi - 2h)/k`.  At the endpoints `1 + u = e^(2 i h)` and `1 + u = e^(-2 i h)`,
and because `A < 1` the circle `|1 + u - 1| = A` misses the origin, so the
continuous argument changes by `-4h`.  Hence the phase advance along one good
arc is

```text
Delta Psi = (n/k)(pi - 2h) + 8h.                                         (19)
```

The Apollonius circle of `u/(1+u)` has largest real part `A/(1+A) < 1/2`, so
`Psi' > n - k > 0` and `Psi` is strictly increasing.  With `R = n/k > 2`, the
advance is `R pi + (8 - 2R) h`, which is above `2 pi` when `R <= 4` and at
least `4 pi` when `R >= 4`.  Every good arc therefore contains a root.  For
`k >= 2` that is two good roots; for `k = 1` the single arc has advance at
least `4 pi` and contains two.  At `A = 0` the identity
`p(t zeta) = omega (1 - t^n)` makes every root good.

### Lemma 2: the amplitude constraint

If `n != 3 k` then `A^2 <= n/k`, and `A <= 2`.

For `n > 3 k`, the elementary symmetric functions vanish below index `k`, so
Newton's identities give `s_k = -k B` and, because `2k < n - k`,
`s_(2k) = k B^2` with `B = omega conj(a)`.  Unimodular roots give
`|s_(2k)| <= n`, hence `A^2 <= n/k`.  More generally
`s_(jk) = (-1)^j k B^j` for `j k < n - k`, which follows from
`-log(1 + B t^k + a t^(n-k) + omega t^n)` truncated below order `n-k`.  With
`j = ceil(n/k) - 2 >= 2` this gives `A^j <= n/k <= j + 2 <= 2^j`, so `A <= 2`.

For `2k < n < 3k`, Newton's identities give `s_k = -k B`,
`s_(n-k) = -(n-k) a`, and `s_(n-2k) = 0`, the last because `n - 2k < k`.  This
is exactly where `n < 3k` is used.  The Gram matrix of the three vectors
`(1)`, `(zeta^k)`, `(zeta^(n-k))` has diagonal `n` and off-diagonal entries
`-k conj(B)`, `-(n-k) conj(a)`, and `0`.  Positive semidefiniteness of its
determinant gives

```text
n^3 - n k^2 A^2 - n (n-k)^2 A^2 >= 0,
A^2 <= n^2 / (k^2 + (n-k)^2) = R^2 / (1 + (R-1)^2).                      (25)
```

Since `R - R^2/(1 + (R-1)^2) = R (R-1)(R-2) / (1 + (R-1)^2) > 0` for `R > 2`,
the claimed bound follows.  The right side of `(25)` is below `2` on
`(2,3)`, so `A < sqrt(2) < 2`.

The exceptional relation `n = 3k` is the only case the lemma omits, and it is
exactly the family where the radial selector can fail at every root.

### Large amplitude, `A > 1`

The curve `1 + u(theta)` winds `k` times around the origin, so
`Psi(theta + 2 pi) - Psi(theta) = 2 pi (n - 2k)`.  With distinct roots every
crossing is transverse, so `N_+ + N_- = n` and `N_+ - N_- = n - 2k`, giving

```text
N_- = k.                                                                 (27)
```

Writing `v = Re u`, condition `Psi' < 0` is equivalent to

```text
v < -(n + (n - 2k) A^2) / (2 (n - k)),
```

and when `A^2 <= n/k` that right side is at most `-A^2/2`, so every negative
crossing has `|1 + u| < 1`.  For `k >= 2` this is two good roots at once.  It
covers `A > 1` with `n != 3k` by Lemma 2, and also `n = 3k` with
`1 < A <= sqrt(3)`.

For `k = 1` and `n >= 4`, Lemma 2 applies and there is exactly one negative
crossing, strictly inside the good arc, which forces `A < 2`.  With
`h = arcsin(A/2)` in `(pi/6, pi/2)` the continuous argument of `1 + u` now
advances from `2h` to `2 pi - 2h`, so

```text
Delta Psi = n (pi - 2h) - 2 (2 pi - 4 h) = (n - 4)(pi - 2h) >= 0.        (31)
```

The signed crossing count on the arc is therefore non-negative, so a positive
crossing accompanies the negative one and the arc holds two good roots.  A
root at an arc endpoint is itself a second good root.

At `A = 1` there is the exact factorisation
`p(z) = (z^k + omega conj(a))(z^(n-k) + a)`.  Every root of the first factor
has `omega + a zeta^k = 0`, which settles `k >= 2`.  For `k = 1` the first
factor gives one good root, and the `n - 1` roots of the second factor are
equally spaced with gap at most `2 pi / 3`, which is the length of the good
arc, so one of them lies in it.  Coincidence of the two occurrences means a
repeated root, where the constant curve suffices.

### The exceptional family `n = 3k`, `A > sqrt(3)`

Here `n >= 4` forces `k >= 2`, and `p(z) = q(z^k)` with

```text
q(w) = w^3 + omega conj(a) w^2 + a w + omega,
|w_1 + w_2 + w_3| = A > sqrt(3).
```

If three unimodular points miss every open semicircle, their successive gaps
`alpha, beta, gamma` lie in `[0, pi]` and sum to `2 pi`, and

```text
|w_1 + w_2 + w_3|^2 = 3 + 2 (cos alpha + cos beta + cos gamma)
                    = 1 - 8 cos(alpha/2) cos(beta/2) cos(gamma/2) <= 1,
```

contradicting `A > sqrt(3)`.  So the three roots lie in an open semicircle.
Let `D < pi` be the shortest containing arc.  Its endpoint roots have sum of
modulus `2 cos(D/2)`, so `A <= 1 + 2 cos(D/2)`.  Since
`sqrt(3) > (1 + sqrt(5))/2 = 1 + 2 cos(2 pi / 5)`, this gives `D < 4 pi / 5`,
so two consecutive roots have separation `delta <= D/2 < 2 pi / 5`.

On the intervening arc, at angular distance `s` from one endpoint,

```text
|w - w_1| |w - w_2| = 4 sin(s/2) sin((delta - s)/2) <= 4 sin^2(delta/4),
```

and the third root is at distance at most `2`.  Hence

```text
|q(w)| <= 8 sin^2(delta/4) < 8 sin^2(pi/10) = 3 - sqrt(5) < 1.           (38)
```

Lifting through `w = z^k` gives a unit-circle arc of length `delta / k` joining
two roots of `p` with the same modulus bound.  The exceptional branch is
positively resolved, with an explicit connector.

## The exact sextic: every lower Abel tail exceeds one

Take `r = 99/100` and

```text
F(z) = z^6 + (5/2) r^2 z^4 + (5/2) r^4 z^2 + r^6.
```

Its normalised quotient is `q(w) = w^3 + (5/2) w^2 + (5/2) w + 1`, which
factors as `(w + 1)(w^2 + (3/2) w + 1)` with roots `-1` and
`-3/4 +- i sqrt(7)/4`, all of modulus one.  So every root of `F` has modulus
`r < 1`.

In the corpus quotient variable `w = z^2` this is the tetranomial
`G(w) = w^3 + (5/2) r^2 w^2 + (5/2) r^4 w + r^6`, with `m = 3`, `r = 2`,
`s = 1`, `b = (5/2) r^4`, `c = r^6`, so the recorded tail is `t = c + b w^s`.
At every quotient root `t = r^6 (1 + (5/2) zeta)` with `|zeta| = 1`, hence
`|t| >= (3/2) r^6`, and exactly

```text
(3/2) r^6 - 1 = 824440448203 / 2000000000000 > 0.                        (41)
```

All six tails are strictly larger than one, and no root is selected by the
recorded tail criterion.  This refutes the selector conjecture recorded in
[CyclicTetranomialCoefficientCase.md](CyclicTetranomialCoefficientCase.md) §4,
whose exact wording is:

> A separate unrestricted probe, which did **not** assume (3), (3a), or (3b),
> accepted 6,348 configurations and never found fewer than two roots with
> `|c+b w^s|<1`.

and

> The next analytic question is whether two roots must satisfy the tail bound
> `|a w^r+w^m|<1` even when the coefficient budget fails.

The two formulations agree because `a w^r + w^m = -(c + b w^s)` at a root.  The
proved conditional theorems of that file are untouched: the coefficient-only
budget `|b| + |c| <= 1` evaluates here to `3342970174401/1000000000000 > 1`, so
no proved hypothesis holds.

Theorem 1 nevertheless settles `F`, with `n = 6`, `k = 2`, `A = 5/2 > sqrt(3)`
and `n = 3k`.  The quotient roots `-1` and `-3/4 + i sqrt(7)/4` are separated
by `delta = arccos(3/4)`, and their lifted arc is a connector of length
`(r/2) arccos(3/4) < pi/5 < 2` with the modulus estimate `(38)`.

The lesson is that a universal tail selector would discard a family that is
easy once the path is allowed to leave the radial star.

### The stored guardrail sextic is also covered

For `p(z) = z^6 + (1/5) z^4 - (1/5) z^2 - 1`, the `r = 1` member of the family
in [AbelControlPolygon.lean](AbelControlPolygon.lean) §5, the corpus records
that the prescribed spoke to the root `1` leaves the lemniscate after scaling,
with the exact midpoint value `p(1/2) = -327/320`.

Here `omega = -1`, `a = -1/5`, `k = 2`, and the four roots with
`zeta^2 = -3/5 +- (4/5) i` satisfy `|omega + a zeta^2|^2 = 4/5` exactly.  All
four of those spokes are safe, with the quantitative bound

```text
|p(t zeta)| <= 1 - t^6 - (1 - 2/sqrt(5)) (t^2 - t^4).
```

The failed prescribed spoke is replaced by a provably admissible pair, and
`A = 1/5 < 1` places the instance in the small-amplitude branch.

## Theorem 3: a pointwise polar-derivative Schur certificate

Let `f(z) = prod_i (z - a_i)` be monic with all roots in the open unit disc,
let `q = f'/n = prod_j (z - c_j)` with `m = n - 1`, and put

```text
q#(z) = prod_j (1 - conj(c_j) z),
sigma_f(z) = (f(z) - z q(z)) / q#(z).
```

Then `sigma_f` is analytic on a neighbourhood of the closed unit disc and
`|sigma_f| < 1` there.  In particular, at every critical point,

```text
|f(c_j)| < prod_l |1 - conj(c_l) c_j|.                                   (46)
```

Proof.  Gauss-Lucas puts every `c_j` in the open disc, because the critical
equation writes `c` as a convex combination of the roots with weights
`|c - a_i|^(-2)`.  So `q#` has no zero on the closed disc and the degree count
`deg(f - z q) <= m` makes `sigma_f` analytic there.  For `|zeta| = 1` set
`H(zeta) = zeta f'(zeta)/f(zeta) = sum_i zeta/(zeta - a_i)`.  Each summand has
real part above `1/2`, because

```text
2 (1 - Re(conj(zeta) a_i)) - |zeta - a_i|^2 = 1 - |a_i|^2 > 0,
```

so `Re H > n/2` and therefore
`|n - H|^2 = |H|^2 + n^2 - 2 n Re H < |H|^2`.  Multiplying by `|f(zeta)|^2` and
using `|zeta f'(zeta)| = |f'(zeta)|` gives
`|n f(zeta) - zeta f'(zeta)| < |f'(zeta)|`, that is
`|f(zeta) - zeta q(zeta)| < |q(zeta)|`.  On the circle `|q#| = |q|`, so the
maximum principle gives the bound on the closed disc.  Evaluating at `c_j`
gives `f(c_j) = sigma_f(c_j) q#(c_j)`.

Assimilation note on strictness.  The return states `(46)` with `<=`.  The
argument proves the strict inequality, since `Re H > n/2` is strict whenever
every root lies in the open disc.  The strict form is what the composition
below uses.

### Composition with the corpus weighted free-point theorem

Choose the analytic root `g = (q#)^(1/m)` with `g(0) = 1`, write
`g = sum_(nu >= 0) b_nu z^nu`, and put
`D(g) = sum_(nu >= 1) (2 nu - 1) |b_nu|^2`.  The equal-weight case of
[FreePointQuadraticAllDegrees.md](FreePointQuadraticAllDegrees.md) gives

```text
(1/m) sum_j |g(c_j)|^2 + D(g) <= 1.                                      (48)
```

Since `|f(c_j)|^(2/m) = |sigma_f(c_j)|^(2/m) |g(c_j)|^2`, the non-negative
interior defect

```text
S(f) = (1/m) sum_j (1 - |sigma_f(c_j)|^(2/m)) |g(c_j)|^2
```

satisfies `(1/m) sum_j |f(c_j)|^(2/m) + S(f) = (1/m) sum_j |g(c_j)|^2`, so

```text
(1/m) sum_j |f(c_j)|^(2/m) + D(g) + S(f) <= 1.                           (50)
```

With `b_1 = -conj((1/n) sum_i a_i)`, which follows from
`sum_j c_j = (m/n) sum_i a_i`, this specialises to

```text
(1/(n-1)) sum_j |f(c_j)|^(2/(n-1)) + |(1/n) sum_i a_i|^2 + S(f) <= 1.    (51)
```

Writing `E = 1 - (1/m) sum_j |f(c_j)|^(2/m)` gives `D(g) <= E` and, by weighted
Cauchy-Schwarz, `sum_(nu >= 1) |b_nu| rho^nu <= sqrt(E rho artanh rho)` for
`0 < rho < 1`.

What this adds over the existing corpus route.  The bridge in
[FreePointTorusPshReduction.md](FreePointTorusPshReduction.md) obtains the
identity `|f(c_j)| = prod_k |1 - conj(c_j) c_k|` only after a plurisubharmonic
maximum principle has moved every root to the distinguished torus, and it
delivers an aggregate bound.  Theorem 3 is a pointwise inequality at the actual
critical points of the actual polynomial, valid for roots anywhere in the open
disc, with a strict deficit `S(f)` that the torus reduction discards.  The two
are complementary: `(48)` remains the corpus input, and `(50)` is the
strengthened output.

These critical-value estimates do not select a root pair and do not control
the length of any curve joining one.

## Consumers

- The corollary closes the four-non-zero-coefficient case on a centred circle,
  a family adjacent to
  [CyclicTetranomialCoefficientCase.md](CyclicTetranomialCoefficientCase.md)
  and disjoint from its coefficient budgets.
- The sextic retires the unrestricted two-tail selector conjecture recorded in
  that file §4, and redirects the residual toward path constructions that are
  not radial.
- `(50)` and `(51)` strengthen
  [FreePointQuadraticAllDegrees.md](FreePointQuadraticAllDegrees.md) by an
  additive non-negative interior term.
- The guardrail instance in [AbelControlPolygon.lean](AbelControlPolygon.lean)
  §5 acquires an explicit safe spoke pair.

## Claim boundary

Theorem 1 requires all roots on one circle centred at the origin and at most
four non-zero coefficients.  For an arbitrary polynomial the missing
coefficients are present, the moment identities `(23)` and `(24)` acquire extra
terms, and the radial control polygon has several independent intermediate
vertices.  Neither the phase argument nor the strengthened critical-value
inequality closes that case.  Unrestricted Erdős #1041 remains open, and
nothing here asserts otherwise.  No Lean module exists for this note; the Lean
row for the Abel identity in `AbelControlPolygon.lean` covers only the
identity, not the selection.

## Replay

```sh
./repo-python formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1041/scripts/check_erdos1041_centred_circle_quadrinomial.py
```

The script emits one JSON line.  Its exact components are the sextic tail
defeat `(41)`, the arc threshold `3 - sqrt(5) < 1` by rational squaring, and
the guardrail amplitudes `4/5` and `6/5` with the midpoint value `-327/320`.
Its sampled components are the paired-quadrinomial alternative over accepted
unit-circle configurations, a direct generator for the `n = 3k` exceptional
family, and the Schur certificate with the composed inequalities `(50)` and
`(51)`.  The sampled components are falsification evidence and carry no
universal authority.
