# Erdős 1041: the exterior coefficient energy of the ancestor component has no uniform floor

## Status

One exact identity, one exact negative result, one measured law. Erdős #1041
remains open; nothing here changes the landed threshold. This note answers the
question that
[ClusterSeparationLowCriticalClosure.md](ClusterSeparationLowCriticalClosure.md)
§"Sharpness and what is left" left open — *"`S` on the ancestor component, as a
function of the elapsed log-level `x` and the arity, is the quantity a proof of
the remaining regime must control"* — and the answer is negative: the mechanism's
own failure inequalities do not control `S` at all.

The separate, positive consequence of the same computation is in
[HyperbolicPackingArityFloor.md](HyperbolicPackingArityFloor.md), which raises
Theorem A from `9/25` to `2/5`.

## 1. The exterior model, exactly

Let `f` be monic of degree `n`, `t` a regular value, `U` a component of
`{|f| < t}` containing `k` roots, `m = n - k`. Let `psi(w) = c(w + beta_0 +
beta_1/w + ...)` be the exterior conformal map of `closure(U)` from `{|w| > 1}`,
`c = cap(closure U)`. The Gronwall area theorem is

```text
Area(U)/pi = c^2 (1 - S),      S = sum_{l >= 1} l |beta_l|^2,          (E1)
```

so the mechanism's normalised area `a` satisfies `a = c^2 (1 - S)` exactly, and
`a <= 1` is sharp only for a disc.

**Exterior fibre form.** `F = f/t` is holomorphic on the exterior `Omega` with a
pole of order `n` at infinity, `|F| = 1` on `partial U`, and `m` zeros in
`Omega`. Schwarz reflection through `|w| = 1` makes `F(psi(w))` a rational map of
degree `n + m`, so with `B` the degree-`m` Blaschke product of
`ExteriorBlaschkeFibreCapacityGap.md` §1 (zeros `a_j = 1/conj(xi_j)`),

```text
f(psi(w)) = t * lambda * w^n / B(w),      |lambda| = 1,   |w| >= 1.     (E2)
```

Matching leading coefficients recovers the corpus's capacity identity
`c^n = t |B(0)| = t prod_j |xi_j|^{-1}`, and differentiating (E2) on `|w| = 1`
recovers the boundary-speed formula `|f'(psi)| |psi'| = t h(theta)`,
`h = n - |B'|`, of that note. Combining with Theorem 2 there,

```text
a  <=  (1 - S) * ( t * k/(2n-k) )^{2/n}   <=  1 - S,                    (E3)
```

which is the exact form of the cap the lane was asked to check. For `k = n`
(`B = 1`) (E2) collapses to `psi(w) = Lambda^{-1}(t^{1/n} w)` with
`Lambda = f^{1/n}`, so `c = t^{1/n}` exactly and

```text
S = sum_{l >= 1} l |kappa_l|^2 t^{-2(l+1)/n},                           (E4)
```

`kappa_l` the Laurent coefficients of the inverse of `f^{1/n}` at infinity. The
first one is `kappa_1 = V/2`, `V = (1/n) sum_i (r_i - mean)^2` the complex
variance of the roots, giving `S >= |V|^2/(4 t^{4/n})`: a quantitative Pólya
deficit, but one that vanishes on every rotationally symmetric configuration.

## 2. The exact model family

Take `f = z^n - q` with `0 < q < 1`, at level `t = 1`. The only critical point is
`0`, with `|f(0)| = q`, so `{|f| <= 1}` is a single Jordan domain holding all
`k = n` roots, `cap = 1`, and (E4) is summable in closed form:

```text
psi(w) = (w^n + q)^{1/n},   beta_{jn-1} = C(1/n, j) q^j,
S(n,q) = sum_{j >= 1} (jn - 1) C(1/n, j)^2 q^{2j}.                      (E5)
```

The uniformising Blaschke product is `B_hat(z) = (z^n - sigma^n)/(1 - sigma^n
z^n)` with `sigma = q^{1/n}`, so the `n` roots sit at pseudohyperbolic radius
`q^{1/n}` about the critical point `h = 0`, all `lam_j = x/n` with
`x = log(1/q) = log(t/mu)`, and the adjacent pseudohyperbolic distance is
`rho(n,q) = r|1-w|/|1-r^2 w|`, `r = q^{1/n}`, `w = exp(2 pi i/n)`. For `n = 2`
the separation threshold is the exact identity `q = tanh(1/a)`, i.e. `x <=
tau(a)` — the corpus's `mu/t >= 0.7635` for two-root components, in closed form,
and strictly below the corpus relaxation `Lambda(2,a)`.

At the birth level `q = 1` (E5) reproduces the corpus's own petal numbers,
`S = 0.3600` at `n = 2` rising to `1/2` as `n -> infinity`.

## 3. The negative result

> **Theorem E.** For every `s_0 > 0` there is a squarefree monic polynomial `f`
> with every root in the open unit disc, a level `t <= 1`, and a component `C`
> of `{|f| < t}` such that
>
> * `C` holds `k >= 2` roots, pairwise at hyperbolic distance `>= d_min(a)` in
>   the uniformisation of `C`, `a = Area(C)/pi`;
> * there is `h in C` with `|f(h)| = mu = min_c |f(c)|`, with
>   `lam_j = -log rho(h, b_j) <= delta(a)/2` for every root, and
>   `sum_j lam_j = x = log(t/mu)` exactly;
> * every critical value of `f` inside `C` has modulus `>= mu`;
>
> and yet `S < s_0`. Concretely, taking `f = z^n - q(n)` at `t = 1` with `q(n)`
> the self-consistent separation threshold,
>
> ```text
> S(n) = (1/n) log(1/(1 - q^2)) (1 + o(1)),   q(n) -> 0.65131,
> ```
>
> so `S -> 0` while `x -> 0.42879` and `a -> 1`.

*Proof.* (E5) plus the separation and COVER computations above; every clause is
an identity in `(n,q)`. The checker verifies each row. ∎

Numbers on that family (self-consistent `a = 1 - S`; `k = n`):

| `k` | `q` | `x` | `S` | `S·k` | `a` |
|---|---|---|---|---|---|
| 2 | 0.85880 | 0.15222 | 0.224054 | 0.4481 | 0.77595 |
| 4 | 0.75618 | 0.27947 | 0.137419 | 0.5497 | 0.86258 |
| 7 | 0.70558 | 0.34874 | 0.078556 | 0.5499 | 0.92144 |
| 10 | 0.68730 | 0.37498 | 0.054900 | 0.5490 | 0.94510 |
| 100 | 0.65427 | 0.42423 | 0.005508 | 0.5508 | 0.99449 |
| 1000 | 0.65140 | 0.42863 | 0.000551 | 0.5514 | 0.99945 |

**Honesty boundary.** On this family Erdős 1041 is trivially true: two adjacent
roots are `2 q^{1/n} sin(pi/n) < 2` apart and the segment between them stays in
`{|f| < 1}`. So the family is not a failure trajectory; the Bergman certificate
of Lemma 1 is simply very lossy on it. What Theorem E kills is the *derivation*
of a floor `S >= s_0` from the mechanism's own hypotheses — a genuine floor would
have to come from an ingredient the mechanism does not currently carry (the
short-curve conclusion itself, or the polynomial-geometry data behind it), not
from `(x, a, k)` plus separation.

## 4. What is measured, and what it buys

The only floor the data supports is `k`-shaped:

```text
0.448 <= S * k <= 0.552        on the model family at threshold separation,
```

with the lower end at `k = 2` and the limit `S k -> log(1/(1-q^2)) = 0.5514`.
An independent instrument — boundary tracing of `{|f| = t}` by continuation in
`arg f`, area by Green's theorem, capacity by Symm's integral equation, and
pseudohyperbolic root separations from the component's Green function solved by
Vandermonde-with-Arnoldi least squares, validated against
`sum_i g_C(z, r_i) = log(t/|f(z)|)` to `1e-14` — reproduces the `k = 2` row
(`S = 0.224482`, `a = 0.77526`, `rho = 0.99714` against the required `0.99712`)
from an adversarial search over quadratics, and reproduces (E5) to machine
precision at `n = 2,3,5,7`.

**A `k`-shaped floor is worth nothing in the comparison ODE.** The cap becomes
`a <= 1 - nu/k` with `k` the *actual* arity, and the mechanism bounds arity only
from below; the adversary declares a large terminal arity, the cap goes to `1`,
and the growth term still only sees `k_lower`. Measured on the `9/25`
mechanism with `nu = 1/3`: `X` falls from `0.99364` to `0.99284`, i.e. the
threshold moves from `0.37023` to `0.37052`. That is noise.

**A floor uniform in `k` would be worth a lot.** Re-running the comparison ODE
with the cap `a <= 1 - s_0` (floating; the corpus's own `9/25` mechanism, and
the packing-sharpened mechanism of the sibling note):

| `s_0` | `mu` ceiling, `9/25` mechanism | `mu` ceiling, packing mechanism |
|---|---|---|
| 0 | 0.37023 | 0.40912 |
| 0.05 | 0.41336 | 0.44231 |
| 0.10 | 0.45889 | 0.47786 |
| 0.15 | 0.50660 | 0.51611 |
| 0.20 | 0.55608 | 0.55798 |
| 0.25 | 0.60681 | 0.60681 |

(These are floating suprema of the comparison ODE, not certificates; the
certified constant sits about `2%` above the floating supremum.)

## 5. Claim boundary

(E1)–(E5) are ordinary identities; (E2) is Schwarz reflection and should be
assumed known. Theorem E is an exact statement about an explicit family, checked
at 40 digits, not Lean-checked and not independently reviewed. The `S·k` band and
the conditional threshold table are measurements, not theorems: the band comes
from one two-parameter family plus an adversarial search at `k = 2` and `k = n`
with `n <= 10`, and components with `2 <= k < n` inside a higher-degree
polynomial were only spot-checked. Erdős #1041 remains open.

## 6. Replay

```sh
./repo-python formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1041/scripts/check_erdos1041_exterior_energy_floor.py
./repo-python formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1041/scripts/check_erdos1041_exterior_energy_floor.py --ode
```

One JSON line; `infimum_S_observed` is the negative result and
`S_times_k_range` the measured law. `--ode` adds the conditional threshold table
and is slow.
