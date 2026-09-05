# Erdős 1041 for every polynomial with least critical value at most 197/1000

## Status

Ordinary complete proof of an unconditional all-degree parent regime, with an
exact rational certificate. Not Lean-checked, not independently reviewed.
Current through the 2026-09-05 eight-return assimilation. Erdős 1041 itself
remains open.

The mechanism came from the eighth return of batch
`erdos1041_20260905_eight_return_stream_01`, which proved the threshold `1/8`
by a scalar potential. Its certificate replays exactly here. The assimilation
delta is the exact comparison-ODE form of the same two inequalities, which
raises the threshold to `197/1000` in every degree and to larger values at
fixed small degree, together with the exact reason the mechanism stops short
of `1/5`.

## Theorem

Let `f` be a squarefree monic polynomial of degree `n >= 2`, and put

```text
mu = min{ |f(c)| : f'(c) = 0 } > 0.
```

> **Theorem A.** If `mu <= 197/1000`, then two distinct roots of `f` are
> joined by a rectifiable curve inside `{|f| < 1}` of length strictly less
> than `2`.

No hypothesis is placed on the root locations, on the number of roots in any
component, or on any component capacity. A repeated root gives the constant
curve, so the squarefree assumption is the nontrivial branch.

> **Corollary B (scale-free form).** Every squarefree monic `f` has two
> distinct roots joined inside `{|f| < (1000/197) mu}` by a curve of length
> below `2 ((1000/197) mu)^(1/n)`.

*Proof of the corollary.* Apply Theorem A to `g(z) = s^(-n) f(sz)` with
`s = ((1000/197) mu)^(1/n)`, whose least critical modulus is `197/1000`, and
scale back. ∎

> **Theorem C (fixed degree).** At degree `n = 4, 5, 6, 7` the same argument,
> using also the arity cap `k <= n` and the Pólya cap
> `Area(K_t)/pi <= t^(2/n)`, certifies the thresholds `mu <= 1/3`, `3/10`,
> `1/4`, `199/1000` respectively (quick-mode certificate); the floating values
> of the mechanism are `0.583`, `0.461`, `0.314`, `0.201`, and `0.688` at
> `n = 3`, which is already solved.

Every consequence for open-unit-disc roots is immediate: `mu <= 197/1000`
is a condition on the critical spectrum alone, and the curve lies in the open
unit lemniscate.

## What the corpus had

`UnconditionalConstantFactorBound.md` proves the parent under four lattices:
`mu <= 1/2` with first-merge arity `k >= 17`, `mu <= 1/4` with `k >= 12`,
`mu <= 1/8` with `k >= 10`, `mu <= 1/64` with `k >= 10`, each with a
capacity-cutoff table for the lower arities. All of them keep an arity or a
capacity hypothesis. Theorem A removes both at `mu <= 197/1000`; those rows
remain correct and remain useful as component-level information above that
threshold.

## The two failure inequalities

Write `K_t = {|f| <= t}` and, for `t > mu`,

```text
x = log(t/mu),        a(x) = Area(K_t)/pi.
```

The area function is absolutely continuous with `a'(x) = t A'(t)/pi` almost
everywhere by the coarea formula, and `a(x) <= t^(2/n) <= 1` while `t < 1`
(Pólya).

Assume, for contradiction, that no two distinct roots are joined inside
`{|f| < 1}` by a curve of length below `2`.

Choose a least-critical point `c*`, and let `Gamma` be the union of two
descending inverse arcs from `c*` into two distinct one-root lobes of
`{|f| < mu}`: a compact connected subset of `K_mu` containing two distinct
roots. For `t > mu` let `C_t` be the component of `{|f| < t}` containing
`Gamma` and `k(t) >= 2` its root count. The set `Gamma` is fixed, so every
`C_t` is an ancestor of the same merger.

### COVER failure forces arity

Uniformise a regular `C_t` by the disc; `f/t` becomes a Blaschke product of
degree `k`. For `h in Gamma`,

```text
prod_j rho_{C_t}(h, a_j) = |f(h)|/t <= mu/t = e^(-x),
```

so some root has pseudohyperbolic distance at most `e^(-x/k)` from `h`. The
one-root Bergman bound (`R2MergeNodeSeparation.md`) gives a path in `C_t`
from `h` to that root of squared length at most `a(x) log(1/(1-e^(-2x/k)))`.
If this is below `1` for every `h in Gamma`, the closed sets
`S_j = {h in Gamma : d_{C_t}(h, a_j) <= 1}` cover the connected set `Gamma`
and two of them meet (`visibility_overlap_reduction_to_a_one_root_statement`),
giving a root-to-root path of length at most `2` inside `C_t`; if a single
`S_j` covers `Gamma` it already contains the other root of `Gamma`. Either way
the length is strictly below `2` after shrinking the radius, and `C_t` lies in
`{|f| < 1}` for `t < 1`. Hence failure forces, at every regular `x` with
`mu e^x < 1`,

```text
k(x) >= 2x / delta(a(x)),        delta(a) = -log(1 - e^(-1/a)).          (1)
```

### Boundary-hop failure forces area growth

Fix a regular level `t` and a direction `theta` avoiding critical-value
arguments. The `k` lifts of the value segment `[0, t e^(i theta)]` inside
`C_t` run from the `k` roots to `k` distinct boundary points. Split each at
level `mu`.

*Low part.* Below `mu` each lift is the complete radial image
`phi_i([0, e^(i theta)))` under the conformal map `phi_i` of the one-root
lobe `U_i`. For a univalent `phi(z) = b_0 + sum b_l z^l` on the disc,

```text
(1/2pi) int_0^{2pi} ( int_0^1 |phi'(r e^(i theta))| dr )^2 dtheta
  <= sum_l l^2 |b_l|^2 / (2l-1) <= sum_l l |b_l|^2 = Area(phi(D))/pi,      (2)
```

by Cauchy--Schwarz in `r` and Parseval. This replaces the pointwise Koebe
estimate of the corpus construction and removes its `(1-r)^(-2)` factor.
Averaging over `theta` and summing over the `k` lobes,

```text
M_low <= sqrt(k A_0 / pi),        A_0 = sum_i Area(U_i) <= Area(C_t).
```

*High part.* By coarea in the level variable and the per-component perimeter
inequality `H^1({|f|=u} cap C_t)^2 <= 2 pi k u A_C'(u)` (Lemma 1 of
`UnconditionalConstantFactorBound.md`),

```text
M_high <= sqrt( k x (Area(C_t) - A_0) / (2 pi) ).
```

Cauchy--Schwarz over the two parts gives the mean total lift length

```text
M(t) <= sqrt( k a(x) (x + 2) / 2 ).                                       (3)
```

*Hop.* Choose `theta` with total lift length at most `M(t)`, order the `k`
boundary points cyclically along the Jordan curve `partial C_t`, and join
consecutive roots by lift, boundary arc, reversed lift. These `k` curves lie
in `closure(C_t) subset {|f| < 1}` and join distinct roots, so under the
failure hypothesis each has length at least `2`:

```text
2k <= 2 M(t) + P(t),        P(t) = H^1(partial C_t).
```

The perimeter inequality applied to `C_t` as a component of `K_t`, with the
global area derivative, gives `P(t)^2 <= 2 pi^2 k a'(x)`. Therefore

```text
a'(x) >= (1/(2 pi^2)) [ 2 sqrt(k) - sqrt(2 a(x)(x+2)) ]_+^2 =: G(x, a(x)),   (4)
```

with `k = k(x)` subject to (1). Since the bracket increases in `k`, (4) holds
with `k = max(2, 2x/delta(a))`, and then `G` is decreasing in `a`.

## The returned scalar potential: `1/8`

Multiply (4) by `delta(a)` and substitute (1). Because `a delta(a) <= delta(1)
=: delta_* = -log(1 - e^(-1)) < 459/1000` for `a <= 1`,

```text
d/dx V(a(x)) >= (1/pi^2) [ 2 sqrt(x) - sqrt(delta_*(x+2)) ]_+^2,
V(a) = int_0^a delta.
```

Integrating from `0` to `X < log(1/mu)` and using `V(a(X)) - V(a(0)) <= V(1)`,
the return's Lemma 6.1 certifies with exact rational arithmetic that the
forcing integral at `X_0 = 2079/1000` exceeds `7/40 > V(1)`, while
`log 8 > 842/405 > X_0`. Hence `mu <= 1/8` is contradictory. The checker
replays this certificate verbatim.

The relaxation `a delta(a) <= delta_*` is exactly tight only at `a = 1`, so
the potential method underestimates the forcing whenever the area is below
the cap.

## The exact comparison: `197/1000`

Keep the differential inequality (4) itself. A counterexample's area function
satisfies `a' >= G(x, a)` almost everywhere, is nondecreasing, and stays at
or below `1` while `t < 1`. Three facts make it a rigorous comparison:

- `G(x, a)` is decreasing in `a`;
- on a cell `[x_i, x_{i+1}]`, the bound obtained from (1) at `x_i` and from
  the subtracted term at `x_{i+1}` is a valid lower bound for `G` throughout
  the cell (the `k`-term increases in `x`, the subtracted term increases in
  `x`), and it is still decreasing in `a`;
- hence `a(x_{i+1}) >= a(x_i) + h G_cell(a(x_{i+1}))`, and the unique zero of
  `phi(a) = a - a(x_i) - h G_cell(a)` is a lower bound for `a(x_{i+1})`. Any
  `a` with `phi(a) < 0` lies below that zero, so a bisection bracket's low end
  is rigorous.

The initial area is unknown and the hitting time of the comparison solution
is not monotone in it: a tiny initial area forces enormous arity and the
trajectory shoots up to a common attractor, while a large initial area is
contradicted almost at once. So the certificate covers the initial condition
by a geometric grid `alpha_0 = 10^-6 < ... < 1`. On `[0, x_s]` with
`x_s = 3/10^5` every trajectory grows at least `c x_s >= alpha_0` for the
explicit `c = (49/968)(2 sqrt 2 - sqrt(2(x_s+2)))^2`, so `a(x_s)` lies in some
grid cell `[alpha_j, alpha_{j+1}]` and is bounded below by the comparison
solution started at `(x_s, alpha_j)`. The certified `X_cert` is the largest
grid hitting time of the cap `a > 1`, and the theorem holds for every
`mu_* <= e^(-X_cert)`.

Every transcendental quantity is bounded in the safe direction by rational
arithmetic: `exp` from below by a truncated Taylor series (with repeated
squaring for large arguments, capped at `e^64`), `exp` from above by the
series plus a geometric tail, `delta(a) = sum_j e^(-j/a)/j` from above by
forty terms plus a geometric tail, square roots by integer square roots on a
`10^-12` grid, `1/(2 pi^2) > 49/968`. The step is `1/800` with geometric
cells while `x` is small; every intermediate rational is floored onto the
grid.

The checker's quick mode (`--quick`, step `1/100`, nine grid points) certifies
`X_cert < 1.6244`, hence `mu <= 197/1000`. The floating supremum of the
mechanism is `X_* = 1.6100` at initial area about `0.056`, attained on a
trajectory that rides with forced arity between six and seven and area growth
near `0.4` per unit of `x`; since `e^(-1.6100) = 0.19989 < 1/5`, the
threshold `1/5` is unreachable by this mechanism with any certificate.

## Fixed degree

At degree `n` two more facts hold: the arity cap `k(x) <= n`, so (1) forces
`a(x) >= delta^(-1)(2x/n)` outright (if `delta(a) < 2x/n` then COVER wins),
and the Pólya cap `a(x) <= (mu e^x)^(2/n)`. The contradiction then comes
earlier, and the certificate selects the largest rational threshold on a
candidate list that survives every grid start with all levels below `1`.

| degree | floating threshold of the mechanism | certified (quick mode) |
|---|---|---|
| 3 | 0.688 | (degree three is solved) |
| 4 | 0.583 | 1/3 |
| 5 | 0.461 | 3/10 |
| 6 | 0.314 | 1/4 |
| 7 | 0.201 | 199/1000 |
| >= 8 | 0.19989 | 197/1000 |

The gap between the floating and certified columns at `n = 4, 5, 6` is
discretisation loss in quick mode, not mathematics; the full-mode run narrows
it.

## Why this is not the parent theorem

The regime `197/1000 < mu < 1` is untouched. The mechanism needs a failure
window `(mu, 1)` of logarithmic length about `1.61`; as `mu` approaches `1`
the window closes, which is exactly the near-Fekete shell studied elsewhere
in this directory. Neither inequality alone is the obstruction: the pair is
sharp as a pair on the attractor trajectory described above. A different
input, most likely one that retains component capacity or the critical-value
spectrum above the least value, is required for the remaining regime.

The sixth return of the same batch proved the same shape of statement with
threshold `2^(-40)` through a two-level capacity argument; it is superseded
here and its capacity content is landed separately in
`SharpSymmetricMergeEnvelope.md`.

## Replay

```sh
./repo-python formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1041/scripts/check_erdos1041_low_critical_potential_closure.py --quick
./repo-python formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1041/scripts/check_erdos1041_low_critical_potential_closure.py
```

The first form finishes in seconds and certifies every constant stated above.
The second uses step `1/800` and twelve grid points and reports the tighter
`X_cert` and per-degree thresholds it can certify; both print one JSON line
whose `all_degree.mu_threshold` and `per_degree_thresholds` fields are the
theorem constants for that run.
