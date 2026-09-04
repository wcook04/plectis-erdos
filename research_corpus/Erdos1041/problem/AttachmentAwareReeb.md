# Erdős #1041: the Reeb lane closes, and its ceiling is exactly `min_c L(c)`

Status: complete ordinary proof, exact rational checker, focused Lean kernel.
2026-08-25. **This does not prove Erdős #1041.** It closes the topology
producer `ray_separatrix_reeb_decomposition`, proves that closing it buys
nothing metric, and hands the surviving obligation back to
`CriticalTreeLengthCharge.md` (F) in an explicit new form.

## 0. What was open

`open_producers::ray_separatrix_reeb_decomposition` (priority 3):

> Prove that a proper planar Morse exhaustion with no saddle-to-saddle gradient
> connections, cut along all saddle separatrices, decomposes the relevant
> truncated component into genuine regular strips plus arbitrarily small saddle
> gluing neighborhoods.

Two things are proved below. The decomposition is real (§1). And it is
metrically inert: once strip representatives are required to attach with
vanishing local cost, they are forced onto the critical-value rays, so the best
locally glued Newton skeleton is exactly the canonical critical inverse-ray
tree (§3). Independent strip averaging supplies no saving, which is why the
`4/25` Cassini deficit already on file could not be repaired by better local
Morse bookkeeping.

## 1. Theorem 1 — the slit-sheet decomposition

Let `f` be monic and let `U` be a connected component of `{|f| < 1}` containing
`k >= 2` roots. Say `U` is **ray separated** when

1. every critical point of `f` in `U` is simple;
2. the critical values `v_c = f(c)`, `c in Crit(f) cap U`, are nonzero;
3. their arguments are pairwise distinct;
4. their moduli are pairwise distinct.

> **Theorem 1.** Let `U` be ray separated. Write `v_c = rho_c e^{i theta_c}`.
>
> **(1a) Morse exhaustion.** `u = -log|f|` is a proper excellent Morse function
> on `U \ f^{-1}(0)`; every finite critical point is a nondegenerate saddle, and
> there are exactly `k - 1` of them.
>
> **(1b) Genuine strips.** Cut the value disk along the complete critical rays
> `R = union_c {r e^{i theta_c} : 0 < r < 1}`. For every component `W` of
> `D \ (R union {0})` and every component `S` of `f^{-1}(W) cap U`, the map
> `f : S -> W` is biholomorphic, and
> `z -> (-log|f(z)|, arg f(z))` is a real-analytic diffeomorphism of `S` onto
> `(0, infinity) x (theta_-, theta_+)`. Truncating the first coordinate gives a
> genuine finite Euclidean strip.
>
> **(1c) Sheet tree.** Put `J_c = {r e^{i theta_c} : rho_c <= r < 1}` and
> `D† = D \ union_c J_c`. Then `D†` is star-shaped about `0`, hence simply
> connected, and `f : f^{-1}(D†) cap U -> D†` splits into exactly `k` conformal
> sheets, one per root. At each `v_c` exactly two sheets are exchanged; joining
> the corresponding root labels gives a graph `T_f` with `k` vertices and
> `k - 1` edges which is a **tree**.
>
> **(1d) Geometric realisation.** The inward value segment
> `I_c = {t v_c : 0 <= t <= 1}` has two inverse lifts, starting at two distinct
> roots and converging to `c`; their union `A_c` is the canonical descending
> root-to-root arc through `c`, contained in `{|f| <= rho_c} subset U`. The
> union `T_f^geo = union_c A_c` is an embedded realisation of `T_f`, so
> `H^1(T_f^geo) = sum_c L(c)` with `L(c) = H^1(A_c)`.
>
> **(1e) Saddle neighbourhoods.** For small `delta`, the component `N_c(delta)`
> of `f^{-1}(B(v_c, delta))` containing `c` satisfies
> `diam N_c(delta) <= C_c sqrt(delta)`, and any two prescribed incident
> separatrix points in it are joined inside it with length `<= C_c sqrt(delta)`.

*Proof.* A component of a polynomial sublevel set is simply connected (maximum
principle; `VisibilityOverlapReduction.md` §3(c)), so `f : U -> D` is proper
holomorphic of degree `k`. Riemann–Hurwitz for a proper degree-`k` map of disks,
`chi(U) = k chi(D) - b`, gives `b = k - 1`; with hypothesis 1 that is `k - 1`
critical points. This much is already recorded in
`CriticalTreeLengthCharge.md` §"Component uniformization".

Near a simple `c` the holomorphic Morse lemma gives a coordinate `zeta` with
`f = v_c + zeta^2`, so
`-log|f| = -log|v_c| - Re(zeta^2/v_c) + O(|zeta|^3)`, whose real Hessian has
signature `(1,1)`: a nondegenerate saddle. Hypothesis 4 separates the Morse
levels. This gives (1a), and (1e) follows because `N_c(delta) = {|zeta| < sqrt
delta}` in that coordinate and the inverse coordinate has bounded derivative on
a fixed small disk.

For (1b): each component `W` is an open sector containing no critical value,
because every critical value lies on a removed ray. So `f` restricted to
`f^{-1}(W) cap U` is an unbranched covering of a simply connected base, and each
component maps biholomorphically. Log-polar coordinates
`r e^{i theta} -> (-log r, theta)` carry `W` onto `(0, infinity) x (theta_-,
theta_+)`.

For (1c), star-shapedness: let `w in D†` and `0 <= s <= 1`. Scaling preserves
`arg w`. If `arg w` is not a critical argument then `[0, w]` meets no slit. If
`arg w = theta_c`, then `w notin J_c` forces `|w| < rho_c`, hence
`|s w| < rho_c` and `s w notin J_c`; by hypothesis 3 no other slit has that
argument. So `[0, w] subset D†`. There are no branch values in `D†`, so `f` is
an unbranched `k`-fold covering of a simply connected base and splits into `k`
sheets; `0 in D†` because every slit starts at radius `rho_c > 0`, so each sheet
carries exactly one root. Local monodromy at a simple critical value is a
transposition. The monodromy action is transitive, since deleting finitely many
fibres from the connected domain `U` leaves a connected covering space; so the
`k - 1` transpositions generate a transitive subgroup of `S_k`, which says
exactly that their graph is connected. A connected graph on `k` vertices with
`k - 1` edges is a tree.

For (1d): by hypothesis 3 the open segment `I_c \ {v_c}` meets no slit and no
other critical value, so the two exchanged sheets give two inverse branches
there; the square-root model shows both converge to `c`, and each starts at the
root over `0`. Each half-arc is injective because distinct parameters have
distinct `f`-values. Two arcs at different critical points can meet away from a
root only if one nonzero value lies on two distinct critical rays, which
hypothesis 3 forbids. Along `I_c`, `|f| = t rho_c <= rho_c`. ∎

## 2. Theorem 2 — attachment rigidity, with the exact window

> **Theorem 2.** Let `gamma` be a nonsingular Newton trajectory,
> `gamma' = -f(gamma)/f'(gamma)`. Then
>
> ```text
> f(gamma(t)) = e^{-t} f(gamma(0)),
> ```
>
> so `arg f(gamma)` is constant, say `theta`. Write `Delta = theta - theta_c`.
> If `gamma` meets `N_c(delta)` then
>
> ```text
> rho_c |sin Delta| < delta    and    cos Delta > 0        (for delta < rho_c).
> ```
>
> The set of attachable arguments is therefore an interval about `theta_c` of
> Lebesgue measure exactly `2 arcsin(delta/rho_c) <= pi delta / rho_c`.

*Proof.* `d/dt f(gamma) = f'(gamma) gamma' = -f(gamma)`, so `e^t f(gamma(t))` is
constant. If `gamma` meets `N_c(delta)` then its value ray `R_theta` meets
`B(v_c, delta)`, i.e. `dist(v_c, R_theta) < delta`. For a ray from the origin at
angle `theta` and a point `rho_c e^{i theta_c}`, the exact identity

```text
rho_c^2 - 2 rho_c r cos Delta + r^2 - rho_c^2 sin^2 Delta = (r - rho_c cos Delta)^2
```

shows the squared distance is `rho_c^2 sin^2 Delta`, attained at
`r = rho_c cos Delta`, when `cos Delta >= 0`, and `rho_c^2` otherwise. For
`delta < rho_c` the second case is excluded, and the first gives
`rho_c |sin Delta| < delta`. Inverting `sin` on `[-pi/2, pi/2]` gives the
interval and its measure; `arcsin x <= (pi/2) x` on `[0,1]` gives the bound. ∎

> **Theorem 2' (window exponent).** Let `c` be a critical point at which
> `f - v_c` vanishes to order `p >= 2`, so `f(z) - v_c = a(z-c)^p(1 + o(1))`.
> Then a Newton trajectory can meet the physical ball `B(c, eps)` only if
>
> ```text
> |sin Delta| <= (|a| eps^p / rho_c)(1 + o(1)),
> ```
>
> so the attachable angular measure at physical radius `eps` is
> `Theta(eps^p / rho_c)`.

*Proof.* On `|z - c| = eps` the value satisfies `|f - v_c| = |a| eps^p(1+o(1))`,
so entering `B(c, eps)` forces `dist(v_c, R_theta) <= |a| eps^p (1+o(1))`; apply
Theorem 2. ∎

The exponent is the ramification index, not a constant. For a simple saddle it
is `2`; for the extremal family `z^n - r^n`, whose unique hub has `p = n`, it is
`n`. **The attachable fraction of directions degrades fastest exactly where the
problem is tight.** §5 makes that case exact.

## 3. Theorem 3 — the lane ceiling

Call a rectifiable graph a **local Newton skeleton at scale `delta`** when it
joins selected root neighbourhoods, is a finite union of Newton-trajectory
segments outside the root neighbourhoods and the `N_c(delta)`, and confines all
non-trajectory connectors to those shrinking neighbourhoods. Let
`C_pair(delta)` and `C_span(delta)` be the infimal lengths of such skeletons
joining two roots, resp. spanning all `k`.

> **Theorem 3.** For a ray-separated `U`,
>
> ```text
> lim_{delta -> 0} C_pair(delta)  = min_c L(c),
> lim_{delta -> 0} C_span(delta)  = sum_c L(c).
> ```

*Proof.* Contract every root and saddle neighbourhood to a vertex; each
remaining trajectory segment is an incidence edge. By Theorem 2 the arguments of
segments meeting `N_c(delta)` converge to `theta_c`, and only the two sheets
transposed at `v_c` have inverse branches converging to `c` — every other branch
stays a positive distance away. So each limiting root–saddle incidence is a half
edge of the subdivided `T_f`. A pair-joining skeleton therefore projects to a
path in `T_f`, whose limiting length is at least the sum of the corresponding
canonical edge lengths, and the shortest tree path is a single edge; a spanning
skeleton projects onto a connected spanning subgraph of the tree `T_f`, every
edge of which is indispensable. Conversely, truncating the canonical arcs `A_c`
at the marked neighbourhoods costs `O(sqrt delta)` by (1e), and the square-root
local form `z - c = lambda sqrt(w - v_c) + O(w - v_c)` gives the integrable
domination needed for convergence of the truncated lengths. ∎

> **Corollary 3a (lane ceiling).** With `Lam` the two-root lemniscate path
> length of `GenericSufficiencyClosure.md`,
>
> ```text
> Lam(f) <= min_c L(c) <= (1/m) sum_c L(c),
> ```
>
> and the Reeb/strip lane can prove **exactly** the middle statement
> `min_c L(c) < 2`, no more and no less.

The first inequality holds because `A_c` is an admissible competitor for `Lam`;
the second is the averaging already recorded at `CriticalTreeLengthCharge.md`
(A). So a Reeb proof cannot be stronger than the admissible-hub statement, and
by Theorem 3 it is not weaker either. **The strip average is an interior `L^1`
quantity in the angular variable; attachment needs its boundary trace at
`theta_c`, and there is no `L^1`-to-trace implication.** The `4/25` Cassini
deficit of `CassiniAttachmentDeficitLab.md` is that failure made exact, and
Theorem 2 is why no shrinking of the saddle neighbourhood repairs it: shrinking
does not make a generic strip trajectory attachable, it deletes almost all of
them.

## 4. Corollary G — the genericity of Theorem 1 is free

Theorem 1 assumes four conditions. Each is the complement of a proper closed
real-analytic subset of the coefficient space: simple critical points is
`disc(f') != 0`; nonzero critical values is `Res(f, f') != 0`; distinct
arguments is `Im(v_i conj(v_j)) != 0` together with `Re(v_i conj(v_j)) > 0`
excluded; distinct moduli is `|v_i| != |v_j|`. Each condition is achievable, so
each bad set is nowhere dense, and a finite union of nowhere dense sets is
nowhere dense.

> **Corollary G.** The ray-separated polynomials are dense in the compact class
> `K_n` of monic degree-`n` polynomials with all roots in the closed unit disk.
> Hence, by `GenericSufficiencyClosure.md` Theorem L and Corollary S, proving
> `min_c L(c) <= 2` for ray-separated members of `K_n` proves Erdős #1041 in
> degree `n`.

*Proof.* Density is the paragraph above, applied inside the open set of
polynomials with roots in the open disk, whose closure is `K_n`. A ray-separated
`g in K_n` with `min_c L(c) <= 2` has a canonical arc `A_c` joining two roots
inside `{|g| <= rho_c} subset {|g| <= 1}` of length `<= 2`, so `Lam(g) <= 2`.
`{Lam <= 2}` is closed in `K_n` by Theorem L, so `Lam <= 2` on all of `K_n`, and
Corollary S converts that into the strict open-disk statement. ∎

This is the load-bearing composition. Before Theorem L, the four hypotheses were
a debt: a genericity argument had to be transported back, which is the producer
retired at commit `044ac603ad`. They are now free, and the Reeb lane may assume
ray separation without loss.

## 5. Theorem 5 — the exact closest approach on the whole extremal family

> **Theorem 5.** Let `g = z^n - r^n`, `0 < r <= 1`, whose unique critical point
> is `0` with `v = -r^n`. For `R_theta = {t e^{i theta} : t >= 0}` put
> `d_{n,r}(theta) = inf{ |z| : g(z) in R_theta }`. Then
>
> ```text
> d_{n,r}(theta) = r                       if cos theta >= 0,
>                = r |sin theta|^{1/n}     if cos theta <  0.
> ```
>
> Consequently, for `eps < r`, a Newton trajectory of `g` meets `B(0, eps)` if
> and only if
>
> ```text
> cos theta < 0    and    |sin theta| < (eps/r)^n,
> ```
>
> an angular window of measure `2 arcsin((eps/r)^n) ~ 2 (eps/r)^n`.

*Proof.* `g(z) in R_theta` means `z^n = r^n + t e^{i theta}` for some `t >= 0`,
so `|z|^{2n} = |r^n + t e^{i theta}|^2 = r^{2n} + 2 r^n t cos theta + t^2`. With
`Rho = r^n` the identity

```text
Rho^2 + 2 Rho t cos theta + t^2 - Rho^2 sin^2 theta = (t + Rho cos theta)^2
```

shows the minimum over `t >= 0` is `Rho^2 sin^2 theta`, attained at
`t = -Rho cos theta`, when `cos theta < 0`, and `Rho^2` at `t = 0` otherwise.
Take `2n`-th roots. ∎

At `n = 2` this is the Cassini formula `a sqrt(|sin theta|)` and its
`(eps/a)^2` window. The general case is the sharp statement: **on the family
that is extremal for Erdős #1041, the attachable fraction of value-directions is
`(eps/r)^n`.** Any strip-average argument must recover a boundary trace on a set
whose measure vanishes like the `n`-th power of the neighbourhood radius.

## 6. Theorem 4 — the root-star tangent law, and the residual made explicit

`CriticalTreeLengthCharge.md` ends by asking for the object below:

> The next proof step must exploit the cyclic order of the selected critical
> rays together with the argument-principle structure in (C) to control this
> combined charge.

Here it is, exactly.

> **Theorem 4.** Let `a` be a simple root of `f` in a ray-separated `U`, and let
> `c_1, ..., c_d` be the critical points whose canonical arcs are incident to
> `a`. The unit tangent at `a` of `A_{c_i}`, pointing from `a` into the arc, is
> exactly
>
> ```text
> U_a^{(i)} = exp( i ( theta_{c_i} - arg f'(a) ) ).
> ```
>
> Hence, with the real inner product `<z, w> = Re(z conj(w))`,
>
> ```text
> sum_{i=1}^{d} <a, U_a^{(i)}> = Re( a exp(i arg f'(a)) S_a ),
> S_a = sum_{i=1}^{d} exp(-i theta_{c_i}).
> ```

*Proof.* Near a simple root, `f(z) = f'(a)(z - a) + O((z-a)^2)`, and `A_{c_i}` is
parametrised by its value `rho e^{i theta_{c_i}}`, so
`z(rho) - a = rho e^{i theta_{c_i}}/f'(a) + O(rho^2)`. Its direction at `a` is
`theta_{c_i} - arg f'(a)`. The displayed sum is
`sum_i Re(a exp(-i(theta_{c_i} - arg f'(a))))`. ∎

Two immediate readings. The `d` arcs leave `a` in **distinct** directions
exactly when the `theta_{c_i}` are distinct, so ray separation is precisely the
statement that the geometric tree has no tangency at a root. And the endpoint
deficit of `CriticalTreeLengthCharge.md` (D) is now explicit.

> **Corollary 4a (explicit residual).** Summing (D) over the edges of an
> admissible component `C` with `m` edges and root set `V(C)`,
>
> ```text
> sum_{e subset C} D_e = 2 R m + sum_{a in V(C)} Re( a exp(i arg f'(a)) S_a ),
> ```
>
> so the surviving obligation (F), equivalently (A), is exactly
>
> ```text
> 2 R m + sum_{a in V(C)} Re( a exp(i arg f'(a)) S_a )
>       + sum_{e subset C} K_e  >=  0.
> ```

Every term is now named in root positions, the arguments of `f'` at the roots,
the arguments of the critical values, and the signed curvature support. This is
the combined charge as a function of the **cyclic order of the critical rays**,
which is what the corpus asked for. It is a reformulation, not a proof: the
required cancellation is still global across the two sums, and
`CriticalTreeLengthCharge.md` records that `sum_e K_e >= 0` alone is false and
that a root-local split is false.

**Exact check on the Cassini witness.** `f = z^2 - a^2`, `R = a`, `k = 2`, one
critical point `0` with `theta_c = pi`. At the root `a`, `f'(a) = 2a` has
argument `0`, so `S_a = e^{-i pi} = -1` and `U_a = e^{i pi} = -1`, giving
`<a, U_a> = -a` and `R + <a, U_a> = 0`. At `-a`, `arg f'(-a) = pi`, `U = +1`,
again `R + <-a, U> = 0`. So `D_e = 0`, `K_e = 0` on the straight segment, and
(D) reads `2R - L = 0`, i.e. `L = 2a`. The identity is tight on the witness that
kills the strip-average route.

## 7. What this does to the producer graph

`ray_separatrix_reeb_decomposition` is retired: **proved** (Theorem 1, with the
hypotheses free by Corollary G) and **non-decisive** (Corollary 3a). Its content
collapses into the two statements already carried elsewhere:
`min_c L(c) <= 2R` — `admissible_branch_length_reformulation` — and its
componentwise strengthening `critical_point_selection_with_inverse_ray_length_control`,
which is `CriticalTreeLengthCharge.md` (F) and is now written explicitly in
Corollary 4a.

The decisive computational target changes accordingly: certified interval
evaluation of the Corollary 4a charge, in square-root coordinates at every
nearly degenerate saddle. A numerical score based on independent strip averages
is no longer relevant. `negative_results` entries 43, 46, 48 and 49 record four
reproductions of the branch-tracking instrument defect that a coarse
continuation produces at exactly those saddles, so an uncertified scan of this
charge is not admissible evidence.

## 8. What is not first here

* Proper degree-`k` uniformisation of a lemniscate component, Riemann–Hurwitz
  giving `k - 1` critical points, the Blaschke normal form, and the pullback
  identity (G): `CriticalTreeLengthCharge.md` §"Component uniformization", and
  `AffineNormalisedModuli.md` Theorem B for `k = 2`.
* The aggregate (A), the tangent-support identity (B), its Newton
  specialisation (C), the budget identity (D), and the componentwise residual
  (F): `CriticalTreeLengthCharge.md`. Corollary 4a is an explicit evaluation of
  (D)'s endpoint term, not a new inequality.
* Constancy of `arg f(gamma)` along Newton trajectories and the resulting
  no-connection statement: `NewtonFlowRaySeparation.lean`
  (`newtonFlow_value_hasDerivAt`, `samePositiveRay_of_real_exp_decay`,
  `no_newtonConnection_of_not_samePositiveRay`). Theorem 2 adds the
  quantitative window; Theorem 2' adds the ramification exponent.
* Small argument/modulus separating translations: `LevelSeparation.lean`.
* The `4/25` attachment deficit at `a = 9/10` and the refutation of the printed
  spanning-tree propositions: `CassiniAttachmentDeficitLab.md`,
  `CassiniTreeBudget.lean`.
* Convex-hull confinement of the canonical branches: recorded separately in the
  packet.
* Density-of-generic and the closedness of `{Lam <= 2}`:
  `GenericSufficiencyClosure.md`, this directory, commit `044ac603ad`.
* Covering space theory, Riemann–Hurwitz, and the holomorphic Morse lemma are
  classical.

## 9. Claim boundary

**Proved, by ordinary mathematics:** Theorems 1, 2, 2', 3, 4, 5, Corollaries
3a, 4a and G.

**Verified formally** in `AttachmentAwareReeb.lean`: the ray-distance identity
and the attachment window of Theorem 2; the extremal-family minimisation of
Theorem 5 and its window; the tree count of (1c) via `SimpleGraph.IsTree`; the
averaging step of Corollary 3a; and the root-star tangent evaluation of Theorem
4 on the Cassini witness. Riemann–Hurwitz, the monodromy argument, the strip
diffeomorphism, and the limits of Theorem 3 are carried by the ordinary proof.

**Not proved:** Erdős #1041; the componentwise charge (F) in any form; and
nothing here bounds `sum_c L(c)` or `min_c L(c)`. Theorem 3 is a *ceiling*
result — it says the Reeb lane cannot do better than the hub statement, not that
the hub statement is true.

**Not established: novelty.** Theorem 1 is standard covering theory applied to a
lemniscate component; Theorems 2 and 5 are one completed square each; Theorem 4
is a first-order expansion. All should be assumed classical or folklore until a
priority search says otherwise. What is claimed is the use: that the
decomposition is metrically inert, that the genericity is free, and that the
residual has the explicit cyclic-order form of Corollary 4a.

## Replay

```sh
./repo-python formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1041/scripts/check_erdos1041_attachment_aware_reeb.py
./repo-python formal_math/erdos257_period_noncollapse/scripts/lean_fast_build.py --jobs 2 ErdosProblems.Erdos1041.AttachmentAwareReeb
```
