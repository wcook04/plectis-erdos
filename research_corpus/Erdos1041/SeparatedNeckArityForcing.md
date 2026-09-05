# Erdős 1041: hyperbolically separated roots force the neck level, and the neck level forces arity

## Status

Ordinary complete proof of a new unconditional forcing inequality for a
counterexample to Erdős #1041, together with the sharp form of the separation
threshold that the Bergman route already implies, and one consequence for the
comparison ODE of
[LowCriticalPotentialClosure.md](LowCriticalPotentialClosure.md). Not
Lean-checked, not independently reviewed. **Erdős #1041 remains open** and
nothing below claims otherwise. The parent statement is unchanged: a monic
polynomial whose roots lie in the open unit disc has two roots joined inside
`{|f| < 1}` by a curve of length less than `2`.

Consequence, certified in §4: the unconditional all-degree low-critical regime
of `LowCriticalPotentialClosure.md` improves from `mu <= 197/1000` to
**`mu <= 1/5`**, crossing the threshold that file records as unreachable by its
own two forcing inequalities. See §4a: a concurrent, unverified sibling note in
this directory reports a stronger constant by a different second floor.

The new content is Theorem 2 and its corollaries. Everything it is built from
is already in this directory: Theorem C' of
[BergmanGeodesicInvariance.md](BergmanGeodesicInvariance.md), Pólya's area cap
recorded in [LemniscateCapacityBudget.md](LemniscateCapacityBudget.md), the
uniformisation step of
[ConnectedClusterBergman.md](ConnectedClusterBergman.md), and the classical
Möbius triangle inequality for the pseudohyperbolic metric.

Throughout `f` is monic, squarefree, of degree `n >= 2`, with all roots in the
open unit disc, and

> **(FAIL)** no two distinct roots of `f` are joined inside `{|f| < 1}` by a
> rectifiable curve of length below `2`.

## 1. The sharp separation threshold

Write `rho_Omega` for the pseudohyperbolic distance of a simply connected
domain `Omega` and put

```text
rho_*  =  sqrt(1 - e^{-4})   =  0.99079985926082...
s_*    =  (1 - sqrt(1-rho_*^2))/rho_*  =  sqrt(tanh 1)  =  0.87269362089783...
```

> **Theorem 1 (separation).** Assume (FAIL). Let `t in (0,1)` be a regular value
> of `|f|` and let `C` be a component of `{|f| < t}` containing at least two
> roots. Then every pair of distinct roots `a != b` in `C` satisfies
> `rho_C(a,b) >= rho_*`.

*Proof.* `C` is bounded and simply connected. Pólya's cap gives
`Area(C) <= Area{|f| < t} <= pi t^{2/n} <= pi`. Theorem C' of
`BergmanGeodesicInvariance.md` bounds the hyperbolic geodesic `Gamma` of `C`
from `a` to `b` by `length(Gamma)^2 <= (Area(C)/pi) log(1/(1-rho^2))`. If
`rho < rho_*` then `log(1/(1-rho^2)) < 4`, so `length(Gamma) < 2`, and
`Gamma subset C subset {|f| < 1}`, contradicting (FAIL). ∎

Two remarks. First, the threshold is exactly `rho_*` and not the round number
`0.99` used as a working constant elsewhere: `log(1/(1-rho_*^2)) = 4`
identically. Second, `s_*` is the `x`-parameter of
[ChordConditionedBergman.md](ChordConditionedBergman.md) at `rho = rho_*`,
`x = s_*^2 = tanh 1`, and it satisfies the identity

```text
2 s_* / (1 + s_*^2)  =  rho_* ,
```

which is a rational identity in `E = e^2`: with `s_*^2 = (E-1)/(E+1)` the left
side squared is `4 s_*^2/(1+s_*^2)^2 = (E^2-1)/E^2 = 1 - e^{-4}`.

Theorem 1 is not new mathematics; it is Theorem C' read as a dichotomy. It is
stated here because it is the hypothesis Theorem 2 consumes, and because the
sharp constant matters below.

## 2. The neck level of a separated Blaschke product

Fix `t` and `C` as in Theorem 1, let `k >= 2` be the number of roots of `f` in
`C`, and let `phi : D -> C` be a Riemann map. Then `B = f(phi(.))/t` is, up to
a unimodular constant, a finite Blaschke product of degree `k` with simple
zeros `w_1, ..., w_k = phi^{-1}(roots)`, and

```text
|B(z)|  =  product_j rho(z, w_j)                                        (1)
```

for the pseudohyperbolic distance `rho` of the disc. Critical points of `B`
are exactly the preimages of critical points of `f` in `C`.

Put `g(u) = (1-u^2)/u`, strictly decreasing on `(0,1]`, and

```text
G_k    =  (k-1) g(s_*)  =  (k-1)(1 - tanh 1)/sqrt(tanh 1) ,
m_k    =  ( sqrt(G_k^2 + 4) - G_k ) / 2 ,          so  g(m_k) = G_k ,
N_k    =  m_k s_*^{k-1} .                                               (2)
```

`m_2 = s_*` and `N_2 = tanh 1`.

> **Theorem 2 (neck level).** Assume (FAIL), and let `t`, `C`, `k` be as in
> Theorem 1. Then every critical point `c` of `f` lying in `C` satisfies
>
> ```text
> |f(c)|  >=  N_k * t .                                                  (3)
> ```

*Proof.* Write `c~ = phi^{-1}(c)`, so `B'(c~) = 0`, and let
`sigma(z) = (z - c~)/(1 - conj(c~) z)`. Then `B o sigma^{-1}` is a Blaschke
product of degree `k` with zeros `v_j = sigma(w_j)` and a critical point at `0`,
and `|v_j| = rho(c~, w_j)`.

*(a) At most one zero is close.* Suppose `|v_i| < s_*` and `|v_j| < s_*` for
`i != j`. The Möbius triangle inequality
`rho(p,q) <= (rho(p,r)+rho(r,q))/(1+rho(p,r)rho(r,q))` and the monotonicity of
`u -> 2u/(1+u^2)` on `[0,1]` give
`rho(v_i,v_j) < 2 s_*/(1+s_*^2) = rho_*`. Pseudohyperbolic distance is a
conformal invariant, so `rho(w_i,w_j) = rho_C(a_i,a_j) < rho_*`, contradicting
Theorem 1. Hence at most one index has `|v_j| < s_*`.

*(b) The critical equation.* `f` is squarefree, so `B` has simple zeros and no
zero of `B` is a critical point; thus `v_j != 0` for every `j`. From
`(B o sigma^{-1})'/(B o sigma^{-1}) = sum_j (1-|v_j|^2)/((z-v_j)(1-conj(v_j)z))`
evaluated at `z = 0`,

```text
sum_j (1 - |v_j|^2)/v_j  =  0 ,     equivalently
sum_j g(|v_j|) e^{-i arg v_j}  =  0 .                                   (4)
```

*(c) The nearest zero.* Let `m = min_j |v_j|`, attained at `j_0`. By (a),
`|v_j| >= s_*` for every `j != j_0`. Taking the term `j_0` to one side of (4)
and using `g > 0` decreasing,

```text
g(m)  =  | sum_{j != j_0} g(|v_j|) e^{-i arg v_j} |
      <=  sum_{j != j_0} g(|v_j|)  <=  (k-1) g(s_*)  =  G_k ,
```

so `m >= m_k`.

*(d) The product.* By (1) and (a), `|B(c~)| = prod_j |v_j| >= m s_*^{k-1}
>= m_k s_*^{k-1} = N_k`, and `|B(c~)| = |f(c)|/t`. ∎

Certified rational lower bounds for `N_k`, and `X_k = log(1/N_k)`:

| `k` | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 |
|---|---|---|---|---|---|---|---|---|---|
| `N_k >` | 0.76159 | 0.58144 | 0.44592 | 0.34404 | 0.26726 | 0.20911 | 0.16476 | 0.13070 | 0.10433 |
| `X_k <` | 0.27234 | 0.54223 | 0.80760 | 1.06697 | 1.31950 | 1.56488 | 1.80321 | 2.03481 | 2.26015 |

## 3. Three corollaries

> **Corollary 3 (two-root window).** Assume (FAIL). A component of `{|f| < t}`
> with `t <= 1` holding exactly two roots and internal critical value `v`
> satisfies `v >= t tanh 1`. Equivalently: a two-root component born at critical
> value `v` cannot survive past level `v/tanh 1 < 1.31304 v` while remaining
> below level one.

This is (3) at `k = 2`, where `N_2 = tanh 1` and the Blaschke normal form makes
the estimate exact (`|B(c)| = x = v/t`). It recovers, from the neck side, the
scalar content of the persistence-window criterion `(19)` of
`ChordConditionedBergman.md` in the case `d -> 2`, `Area/pi -> 1`.

> **Corollary 4 (compressed critical spectrum).** Assume (FAIL). For every
> regular `t <= 1` and every component `C` of `{|f| < t}` with `k >= 2` roots,
> all critical values of `f` attained in `C` lie in `[N_k t, t)`. Their ratio is
> therefore at most `1/N_k`: at most `1.313` for `k = 2`, `1.720` for `k = 3`,
> `2.242` for `k = 4`, `2.906` for `k = 5`.

> **Corollary 5 (arity forcing).** Assume (FAIL). Let `mu = min |f(c)|` over
> critical points, let `c*` attain it, let `Gamma` be a compact connected subset
> of `{|f| <= mu}` containing `c*` and two distinct roots, and for `t > mu` let
> `C_t` be the component of `{|f| < t}` containing `Gamma`, with `k(t)` roots.
> Then, with `x = log(t/mu)` and `mu e^x < 1`,
>
> ```text
> e^{-x}  >=  N_{k(x)} ,    i.e.    k(x)  >=  K(x) := min{ k >= 2 : N_k <= e^{-x} } .
> ```

*Proof.* `c* in Gamma subset C_t`, so Theorem 2 applies with the critical point
`c*`: `mu = |f(c*)| >= N_{k(t)} t`. `N_k` is strictly decreasing in `k`. ∎

The set `Gamma` is the one built in `LowCriticalPotentialClosure.md` (two
descending inverse arcs from `c*` into two distinct one-root lobes of
`{|f| < mu}`); its existence is exactly the hypothesis used there.

## 4. What this does to the low-critical comparison ODE

`LowCriticalPotentialClosure.md` proves `mu <= 197/1000` by combining two
forcing inequalities under (FAIL): a COVER inequality
`k(x) >= 2x/delta(a(x))` with `delta(a) = -log(1-e^{-1/a})`, and a boundary-hop
inequality `a'(x) >= (1/2pi^2)[2 sqrt(k) - sqrt(2a(x+2))]_+^2` for the
normalised area `a(x) = Area(K_{mu e^x})/pi <= 1`. Corollary 5 is a **third,
independent** lower bound on the same arity `k(x)`, so the certified pipeline
runs verbatim with

```text
k(x, a)  =  max( 2, 2x/delta(a), K(x) ) .
```

The two bounds are complementary rather than comparable. `delta` is increasing,
so the COVER bound is at its **weakest** exactly at the area cap: `2x/delta(a)
<= 4.36042 x` when `a = 1`, and much larger than that when `a` is small.
`K(x)` is a fixed integer schedule independent of `a` — `K(x) = k` exactly on
`X_{k-1} < x <= X_k`, so `k >= 7` from `x > 1.31951`, `k >= 8` from
`x > 1.56489`, `k >= 9` from `x > 1.80322`, `k >= 10` from `x > 2.03482`. So COVER dominates on the early, small-area part of
a trajectory and `K` dominates near the cap, which is where the hitting time is
decided. At `a = 1` and `x = 1.6`, COVER gives `floor(6.976) = 6` and `K` gives
`8`.

`K(x)` uses the area only through `Area(C_t) <= pi t^{2/n} <= pi`, an UPPER
bound; the certificate's `a(x)` is a rigorous LOWER bound for the same area and
must not be substituted into `K`. At fixed degree the Pólya cap
`Area(C_t) <= pi (mu e^x)^{2/n} < pi` is available and makes `K` strictly
larger; that refinement is not used here.

Effect, measured on a float model of the certified scheme (geometric cells,
implicit-Euler lower step, geometric grid of initial areas, step `1/800`):

| | `X_*` | `mu` reachable |
|---|---|---|
| COVER only | `1.6747` | `0.1874` |
| COVER + neck (Theorem 2) | `1.6372` | `0.1945` |
| COVER + neck under the unproved `m >= s_*` of §5 | `1.3197` | `0.2672` |

The float model is coarser than the certificate and its absolute values are not
the certificate's; it only says the gain is real.

The exact rational certificate was then run, in the certified pipeline of
`check_erdos1041_low_critical_potential_closure.py` with `k_lower` replaced by
`max(k_lower, neck_k_lower)` and nothing else changed, quick mode
(step `1/100`, nine grid points):

| run | `X_cert` (exact rational, float view) | largest certified `mu` |
|---|---|---|
| COVER only, quick | `1.624373027130775` | `197/1000` |
| COVER + neck, quick | `1.604373027130775` | `1/5` |

> **Theorem 6.** Every squarefree monic `f` of degree `n >= 2` whose least
> critical-value modulus satisfies `mu <= 1/5` has two distinct roots joined
> inside `{|f| < 1}` by a rectifiable curve of length below `2`.

This is `LowCriticalPotentialClosure.md` Theorem A with `197/1000` replaced by
`1/5`, on the strength of Corollary 5. It crosses the value that file records as
out of reach: *"since `e^{-1.6100} = 0.19989 < 1/5`, the threshold `1/5` is
unreachable by this mechanism"* — true of the COVER/hop pair alone, and no
longer true once the third forcing inequality is added. The exact quick-mode gain
is `0.02` in `X_cert`, and `(1/5) exp(X_cert) < 1` is the certified test.

The full-mode run (step `1/800`, twelve grid points) and the per-degree rows for
`n = 4..7` were not completed in this pass; the per-degree thresholds
`1/3, 3/10, 1/4, 199/1000` stand as recorded and can only improve.

## 4a. Concurrent work in this directory, unverified

An untracked sibling note,
[ClusterSeparationLowCriticalClosure.md](ClusterSeparationLowCriticalClosure.md),
landed in this directory in the same session window and does the same *kind* of
thing to the same ODE — it adds a second arity floor and reruns the certificate —
by a **different** mechanism, the connected-cluster selection rather than the
critical-point equation, and reports a stronger threshold `mu <= 9/25`. Its
floor is `k >= 1 + (2x - delta(a))/tau(a)` with `tau(a) = -log tanh(1/a)`; note
`tau(1) = 0.272345 = X_2` of the table above, so at the area cap its schedule is
`k >~ 7.343 x`, which is exactly the schedule §5 below identifies as what the
unproved sharpening `m >= s_*` would buy through this note's route. Two
independent mechanisms landing on the same slope is worth recording.

**Nothing of that note is verified here.** Concurrent-lab results in this
directory are reported, not verified, and one specific step deserves checking
before the two are composed: the cluster selection bounds a root pair by
`q_C^{2/k}` where `q_C` is the **largest** internal critical value over `t`, and
under failure that yields a lower bound on `q_C`, whereas an arity floor needs
an upper bound on it. If that step is sound, its constant supersedes Theorem 6
and Theorem 6 should be read as a weaker independent confirmation; Theorems 1-5
and Corollaries 3-4 are untouched either way, since they are statements about
neck levels rather than about the ODE.

**Conductor verification, 2026-09-05 (after both notes were complete).** The
step flagged above is not present in the sibling note. Its second floor does not
use the cluster *selection* `q_C^{2/k}` at all: it applies the two-point Bergman
bound `L^2 <= 4a artanh(s^2)` (its Lemma 1) to **every** pair of roots in the
ancestor component, so failure forces every pairwise hyperbolic distance up to
`d_min(a) = 4 artanh(sqrt(tanh(1/a)))`, and then combines that with the COVER
observer through the triangle inequality. No bound on `q_C` enters in either
direction. Its certificate was replayed by the conductor (quick mode, `rc=0`,
`X_cert = 101437302713/100000000000`). Theorem 6 is therefore the weaker
independent confirmation, and `mu <= 9/25` is the landed parent regime. The
neck floor `k >= K(x)` of Corollary 5 was also measured against that note's
floor on its extremal trajectory: at the attractor (`a` between `0.43` and `1`,
`x` up to `1`) it forces `k >= 4` where the pairwise-separation floor already
forces `k` near `7`, so composing the two does not move `9/25`.

## 5. Sharpness of Theorem 2

Step (c) is not tight for `k >= 3`: it discards the angular cancellation in (4).
Symmetric configurations give the exact value `m = r` with
`2 r/ (1+r^2)`-type separation, e.g. for the `k`-fold symmetric product
`B(z) = (z^k - r^k)/(1 - r^k z^k)` the unique critical point is `0` with
`m = r`, and at `rho = rho_*` this gives `m = 0.88897` (`k = 3`) and `0.90841`
(`k = 4`) against the proved `m_3 = 0.76346`, `m_4 = 0.67093`. If the stronger
`m >= s_*` held in general the schedule would become `X_k = k log(1/s_*) =
0.136178 k`, roughly `k >= 7.34 x`, which is far stronger than either existing
forcing inequality: in the same float model of §4 it moves `X_*` to `1.3197`,
i.e. `mu` reachable `0.2672`. That statement is **not proved here and not
asserted**; a dedicated extremal search over separated configurations was
inconclusive (it produced no feasible optimum under its own tolerance), and the
`LEMMA` arm records only that the proved `m_k` holds with slack `0.106` to
`0.359` at `k = 2..5` over `1483..1523` separated samples each. The note
therefore records only the proved `m_k`, and flags **proving or refuting
`m >= s_*` on separated Blaschke zero sets as the highest-value scalar target
adjacent to this route**.

## 6. Claim boundary

**Proved, by ordinary mathematics.** Theorem 1; Theorem 2 with steps (a)-(d);
Corollaries 3, 4, 5; the identity `2 s_*/(1+s_*^2) = rho_*` and
`log(1/(1-rho_*^2)) = 4`; the monotonicity and positivity of `N_k`. Theorem 6 is
proved conditionally on the correctness of the `LowCriticalPotentialClosure.md`
argument it reuses verbatim: this note supplies only the third forcing
inequality and reruns that file's own certified scheme.

**Exact rational certificates.** The enclosures of `tanh 1`, `rho_*^2`, `s_*`,
and the table of `N_k` lower bounds with directed rounding; the rational
identity in `E`; `1/N_2 < 1.31304`; the quick-mode `X_cert` pair
`1.604373027130775` (with neck) against `1.624373027130775` (without) and the
test `(1/5) exp(X_cert) <= 1`.

**Floating, with no proof authority.** The Möbius triangle inequality is
classical and is only falsification-tested here; the critical-equation residual
check; the separated-configuration slack measurements; the entire §4 table,
which is a float model of a certified scheme and not a certificate.

**Not first here.** Theorem C' is `BergmanGeodesicInvariance.md`; the area cap
is Pólya's, recorded in `LemniscateCapacityBudget.md`; the uniformisation and
the identity `prod_j rho(z,w_j) = |B(z)|` are `ConnectedClusterBergman.md`; the
`x = v/t` normal form is `AffineNormalisedModuli.md` via
`ChordConditionedBergman.md`; the COVER/hop pair and the `Gamma` construction
are `LowCriticalPotentialClosure.md`. The critical-point equation for a finite
Blaschke product is classical. No novelty is claimed for any of those; what is
new here is the composition (a)-(d) and the arity schedule it yields.

**Erdős #1041 remains open.** Theorem 2 sharpens the input to an existing
allocation problem. It does not close the regime `197/1000 < mu < 1`, and
negative result 74 of the kill-list (the universal merge-node forcing of the
connected-cluster Bergman certificate is FALSE on `z^n - r^n` at every level and
in every degree) still applies to every purely Bergman/capacity route in the
separated regime.

## Replay

```sh
./repo-python formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1041/scripts/check_erdos1041_separated_neck_arity_forcing.py --part all
```

| arm | what fails it |
|---|---|
| `IDENTITY` | the rational identity in `E` fails, `tanh 1` or `rho_*^2` leaves its enclosure, or `rho_*` fails to exceed `99/100` |
| `SCHEDULE` | an `N_k` lower bound drops below its tabled rational, `N_k` stops decreasing, or `1/N_2 >= 13131/10000` |
| `TRIANGLE` | a sampled triple violates the Möbius triangle inequality |
| `CRITICAL` | the residual of `sum_j (1-|v_j|^2)/v_j` at a computed critical point exceeds `1e-6` |
| `LEMMA` | a `rho_*`-separated Blaschke configuration has a critical point with `m < m_k` or `|B(c)| < N_k` |
| `CLOSURE` | the neck-augmented `certify_all_degree` fails to certify `mu = 1/5`, does not beat the unpatched `X_cert`, or the unpatched pipeline unexpectedly reaches `1/5` on its own |

`CLOSURE` runs in about ten seconds; it imports
`check_erdos1041_low_critical_potential_closure.py` and replaces only its
`k_lower`.
