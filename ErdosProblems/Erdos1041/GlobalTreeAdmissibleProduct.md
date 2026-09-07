# Global tree admissible product for root–critical distances

Status: new exact theorem family, Type-A landed 2026-08-28 (batch 03, return 006,
improved).  Ordinary proof, numerically verified by
`scripts/check_erdos1041_global_tree_admissible_product.py`, not Lean-checked.
This is **not** a proof of unrestricted Erdős #1041 and carries no sublevel
containment; see the claim boundary before consuming it.

## Theorem 1 (incidence product)

Let `f` be monic of degree `n >= 2` with listed zeros `z_1,...,z_n` in the
closed unit disc, and let `c_1,...,c_{n-1}` be the zeros of `f'`, listed with
multiplicity.  Then

```text
R := prod_{i=1}^n prod_{j=1}^{n-1} |z_i - c_j|  <=  1.
```

Equality holds exactly when the listed zero locations are a rotation of the
full set of `n`-th roots of unity; then every critical point is `0` and each
factor equals `1`.

Proof.  For every listed root `z_i`, `f'(z_i) = prod_{k != i} (z_i - z_k)`
(valid with multiplicity: write `f(z) = (z - z_i) h(z)`, `h(z_i) = prod_{k!=i}(z_i - z_k)`),
and `f'(z_i) = n prod_j (z_i - c_j)`.  Hence

```text
n^n R = prod_i |f'(z_i)| = prod_{i<k} |z_i - z_k|^2 = |det V|^2,
```

where `V = (z_i^{j-1})` is the Vandermonde matrix.  Hadamard's inequality,
with row norm `sum_{m=0}^{n-1} |z_i|^{2m} <= n`, gives `|det V| <= n^{n/2}`,
so `R <= 1`.  Equality in Hadamard forces every `|z_i| = 1` and mutually
orthogonal rows, i.e. `sum_{m=0}^{n-1} (z_i conj(z_k))^m = 0` for `i != k`,
which says `z_i / z_k` runs over the non-trivial `n`-th roots of unity.  For
that configuration every critical point of `z^n - omega` is `0`.  Square
case `n = 2`: `R = |z_1 - z_2|^2 / 4 <= 1` with equality at the antipodal
pair, which is the `n = 2` rotation family.  `[]`

Remark.  `R = prod_{j=1}^{n-1} |f(c_j)|`, so Theorem 1 is the corpus's
occupied critical-value product budget (return-004 claim r004_c01,
"product of all critical-value moduli is at most one") re-derived with its
equality case.  The new content of this file is Theorems 2-4.

## Theorem 2 (tree matching)

Fix any tree `T` on `n` vertices (root slots) and any bijection
`lambda: E(T) -> {1,...,n-1}` assigning one critical point to each edge.  For
a bijection `pi: V(T) -> {1,...,n}` put

```text
A(pi) := prod_{uv in E(T)} |z_{pi(u)} - c_{lambda(uv)}| |z_{pi(v)} - c_{lambda(uv)}|.
```

Then some bijection `pi` satisfies `A(pi) <= R^{2/n} <= 1`.

Forest refinement.  For every forest `F` with `m >= 1` edges, every injective
`lambda: E(F) -> J` with `J subset {1,...,n-1}`, `|J| = m`, some `pi` satisfies

```text
A(pi) <= ( prod_{j in J} |f(c_j)| )^{2/n}.
```

Proof.  Over all `n!` bijections, fix a labelled edge `e = uv` carrying label
`j` and a root index `i`.  The factor `|z_i - c_j|` occurs in `A(pi)` exactly
when `pi(u) = i` or `pi(v) = i`: `(n-1)! + (n-1)!` disjoint classes.  Hence

```text
prod_pi A(pi) = prod_{(i,j) labelled} |z_i - c_j|^{2 (n-1)!},
```

and the geometric mean over the `n!` bijections is the labelled incidence
product to the power `2(n-1)!/n! = 2/n`.  Some `A(pi)` does not exceed the
geometric mean.  For the full tree the labelled product is `R`; for the
forest it is `prod_{j in J} prod_i |z_i - c_j| = prod_{j in J} |f(c_j)|`
(moninicity).  Degeneracies included: if some `z_i = c_j` then every
`A(pi)` using that incidence is `0`.  `[]`

## Theorem 3 (exact weighted conservation law)

With `A(pi)` as in Theorem 2 for a tree `T`, define the critical-value-weighted
product

```text
B(pi) := A(pi) / prod_{e in E(T)} |f(c_{lambda(e)})|^{2/n}.
```

Then, for every monic `f` (no root-location hypothesis at all),

```text
prod_{pi} B(pi) = 1   identically,
```

so `min_pi B(pi) <= 1 <= max_pi B(pi)` for every `(T, lambda)`.  On the
extremal families `z^n - omega` (all critical points at the origin, roots a
rotation of the regular `n`-gon) and `z^n - r^n`, every `B(pi) = 1`.

Proof.  `prod_pi A(pi) = R^{2(n-1)!}` by the counting above.  Each label `j`
sits on exactly one edge, so the denominator contributes
`prod_j |f(c_j)|^{(2/n) n!}` in total.  Since
`prod_j |f(c_j)| = prod_{i,j} |z_i - c_j| = R` and `n!/n = (n-1)!`,
`prod_pi B(pi) = R^{2(n-1)! - 2(n-1)!} = 1`.  `[]`

Theorem 3 says the weighted two-arm products over all placements are governed
by an exact conservation law: the geometric mean is pinned at `1` independent
of the polynomial.  The unweighted Theorem 2 is the disc-restricted shadow of
this law via `prod_j |f(c_j)| = R <= 1`.

## Theorem 4 (selector form)

```text
prod_{i=1}^n dist(z_i, Z(f'))  <=  1.
```

Proof.  `dist(z_i, Z(f'))` is the minimum of the `n-1` numbers `|z_i - c_j|`,
hence at most their geometric mean: `rho_i^{n-1} <= prod_j |z_i - c_j|`.
Multiply over `i` and apply Theorem 1.  `[]`

## Claim boundary (read before consuming)

1. **No containment.**  Theorem 2 matches roots to critical points in
   Euclidean distance only.  No straight arm from a matched pair, and no
   other a priori arm, is certified to lie in `{|f| <= 1}`: the corpus
   spoke-visibility no-gos apply unchanged (research packet negative entries
   12, 15, 16, 22, 25; the exact balanced quintic; `CentroidHubCounterexample.md`).
   Consequently the theorem does **not** feed the open producer
   `free_pair_geometric_mean_two_arm_selector`, whose missing premise is
   containment of both hub arms in `{|f| <= Gcrit}`; its Euclidean half
   (`|h - a_i| + |h - a_j| <= 2`) is already occupied by
   `GlobalCriticalTwoNearestBudget.md` and the Lean theorem
   `exists_two_roots_dist_sum_le_two_mul_geomMean`.
2. **Single-point corollaries are dominated.**  At every critical point the
   two nearest listed occurrences satisfy `d_1 + d_2 <= 2 |f(c)|^{1/n}`
   (`BarycentricEnvelope.md` section 3, (F)); any "there exists a pair with
   product `<= |f(c)|^{2/n}`" consequence of Theorems 2-4 is therefore
   occupied.  The non-dominated content is exactly the simultaneous matching
   quantifier: for every `(T, lambda)` at once, not merely per critical point.
3. **Not an admissible product in the corpus sense.**  `(AP)` in
   `AdmissibleCriticalArcProductLab.md` multiplies entrance-arc quotients
   `L(c) / (2 |f(c)|^{1/n})` — inverse-ray arc lengths, not Euclidean
   distances — and the exact hybrid falsifier (actual `0.839217266469` versus
   independently majorized `1.075474341153`) forbids independent child
   majorization in that lane.  Theorem 2 neither implies nor contradicts
   `(AP)`, `(CAQ)`, or `(PGLS)`.
4. **Routing consequence.**  Any future parent-facing consumer of this
   theorem must supply a containment-and-length bridge from Euclidean
   two-arm products to lemniscate arcs.  By the no-gos above that bridge
   cannot be straight spokes; the only source-current machinery that makes
   contained arms at all is the inverse-ray/Newton-transport pair
   (`NewtonFlowTransport.md` T1/T2) with the moved-block budget
   (`PartialClusterPreimagePerimeterIdentity.md` (PP1)-(PP2)), i.e. the tree
   product can at best re-derive the Euclidean skeleton of the occupied
   decomposition `L(c) = (d_a + d_b) + D(c)`.

## Verification

`./repo-python formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1041/scripts/check_erdos1041_global_tree_admissible_product.py`

covers: random `R <= 1` and selector sweeps (degrees 2-8); the exact counting
identity `prod_pi A(pi) = R^{2(n-1)!}` at `n = 3, 4` (30-digit arithmetic);
`min_pi A(pi) <= R^{2/n}` for path and star trees; equality `R = 1` on
regular polygons; the per-critical-point two-nearest budget; the per-spoke
AM-GM certificate with the six-root non-universality witness
`|P(1/2)| = 1.100256... > 1`; the mean radial-lift bound; the weighted-disc
union witness; the root-ray power-series identity; the trinomial closures;
and the component-lifetime coarea identity of
`ComponentLifetimeTransportIdentity.md`.
