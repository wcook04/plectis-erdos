# Erdős 1041: the disk-family critical-value separation theorem

Status: ordinary exact analytic theorem (all degrees `n >= 3`), with a
Lean-checked numerical kernel (`DiskFamilyCriticalValueSeparation.lean`) and a
recorded adversarial falsifier
(`formal_math/probes/erdos1041_disk_family_separation_probe.py`, receipt
`disk_family_critical_value_separation_probe_receipt.json`).  2026-09-02.

This strictly strengthens `FirstMergeCriticalValueSeparationCertificate.md`
(2026-08-30) and, as its `w0 = 0` member, contains the uncapped form of
`FirstTwoCriticalOptimizedBergman.md` and the minimal-hub spectral window of
`MinimalHubWindowJoin.md`.  It is a genuine all-degree sufficient regime.  It
does **not** decide Erdős 1041; the exact residual is stated in §5.

## 1. Statement

Let `f` be monic of degree `n >= 3`, let `c` be a simple non-root critical
point, `v = f(c)`, `rho = |v|^(1/n)`, and normalise

```text
P(w) = f(c + rho w)/v,        P(0) = 1,  P'(0) = 0,  P''(0) != 0,  |lead P| = 1.
```

The other critical points `d_j` of `f` have normalised critical values
`v_j = f(d_j)/v`.  Let `Z` be either local solution of `P(Z(xi)) = 1 - xi^2`,
`Z(0) = 0`, and let `Gamma = Z([-1,1])` be the canonical connector (the two
descending inverse-ray branches from `c`, scaled).

> **Theorem A (disk family).**  Fix a real centre `w0` in `[0,1]` and a radius
> `S > max(w0, 1 - w0)` such that
>
> ```text
> |v_j - w0| >= S        for every other critical point d_j.          (H)
> ```
>
> Put `p = w0 (1 - w0)`, so `0 <= p <= 1/4`.  Then `Z` continues to a
> conformal bijection of an explicit simply connected domain onto the
> component `U` of `{|P - w0| < S}` containing `0`, the endpoints `Z(-1)`,
> `Z(1)` are two distinct roots of `P`, `Gamma` lies in `{|P| <= 1}`, and
>
> ```text
> len(Gamma)^2  <=  2 (S/(n-1))^(2/n) log((S^2 + S + p)/(S^2 - S + p)).   (DF)
> ```
>
> Consequently `f` has two distinct roots joined inside `{|f| <= |v|}` by a
> path of length `rho * len(Gamma)`, which is below `2 rho` whenever
>
> ```text
> C(n, S, p) := (S/(n-1))^(2/n) log((S^2 + S + p)/(S^2 - S + p)) < 2.   (T)
> ```

> **Corollary B (parent-problem regime).**  Let all roots of `f` lie in the
> open unit disk and let `c` be a simple critical point with `|f(c)| < 1`
> (for example any simple minimum-modulus critical point, by the Fekete
> chain `min_c |f(c)| <= R^n < 1`).  If some real centre `w0` in `[0,1]`
> admits a radius `S` satisfying (H) and (T), then Erdős 1041 holds for `f`.

> **Corollary C (uniform thresholds).**  (T) holds for every `n >= 3`, every
> `4/3 <= S <= 2`, and every `p` in `[0, 1/4]`.  Hence:
>
> * (branch centre, `w0 = 1`) `|1 - v_j| >= 4/3` for every `j` suffices in
>   every degree `n >= 3`;
> * (origin centre, `w0 = 0`) `|v_j| >= 4/3` for every `j`, i.e. second
>   critical-value modulus at least `4/3` times the first, suffices in every
>   degree `n >= 3`;
> * (any real centre) `|v_j - w0| >= 4/3` suffices in every degree.
>
> The radius `2` also works in every degree `n >= 3` at either endpoint
> centre, `(2/(n-1))^(2/n) log 3 < 2`.  In degree three the branch centre
> closes already at radius `6/5`: `(3/5)^(2/3) log 11 < 2`.

The former certificate needed `S = 4` at `n = 3`, `S = 3` at `n >= 4`, and
`S = 2` at `n >= 6`, all at the branch centre only.  The degree-free
constant `4/3` is not the limit of the method: (T) at `p = 0` is equivalent
to `log((S+1)/(S-1)) < 2 (n-1)^(2/n) S^(-2/n)`, and the exact per-degree
thresholds `S_n^*(w0)` (smallest `S` with (T)) are

```text
   n      w0=0 or 1     w0=1/4 or 3/4    w0=1/2
   3       1.10892        0.83104         0.63053
   4       1.07318        0.81336         0.62619
   5       1.06981        0.81769         0.64322
   6       1.07347        0.82701         0.66393
  10       1.09994        0.87035         0.73797
  20       1.15255        0.94592         0.84272
 100       1.25415        1.07840         1.00180
 n->oo     coth(1) = 1.313035...  (both endpoint centres)
```

The endpoint threshold is not monotone in the degree: it dips to `1.0698` at
`n = 5` and rises to `coth(1)` because the exterior-fibre factor
`(n-1)^(-2/n)` decays while the logarithmic factor is degree-free.  The
uniform constant `4/3 > coth(1)` is what survives every degree, and the
Lean kernel checks it exactly.

## 2. Proof of Theorem A

**Step 1: the two-sheeted component.**  Write `Q = D(w0, S)`.  By
`S > max(w0, 1-w0)`, both `0` and `1` lie in `Q`, so the real segment
`[0,1]` lies in `Q`.  Let `U` be the component of `P^(-1)(Q)` containing
`0`; it exists because `|P(0) - w0| = 1 - w0 < S`.  The restriction
`P : U -> Q` is proper.  Its only critical point is `0`, because a critical
point `d_j` in `U` would satisfy `|v_j - w0| < S`, contradicting (H).  The
critical point is simple, so the degree of `P|U` is `1 + 1 = 2`, and
Riemann–Hurwitz gives `chi(U) = 2 chi(Q) - 1 = 1`: `U` is simply connected.

**Step 2: the uniformiser.**  On `U` the function `1 - P` has exactly one
zero, the double zero at `0` (its zeros are the fibre of `P|U` over `1`,
which is `{0}` with multiplicity two).  Since `U` is simply connected,
`1 - P = z^2 h(z)` with `h` nonvanishing on `U` admits a single-valued square
root, so `xi(z) = z sqrt(h(z))` is a single-valued analytic function on `U`
with `xi^2 = 1 - P`.  It maps `U` into

```text
Qtilde = { xi : |xi^2 - a| < S },      a = 1 - w0,
```

which is the connected two-fold cover of `D(a, S)` branched at `xi = 0`
(note `0` lies in `D(a,S)` since `a < S`), hence simply connected.  The map
`xi` is proper (`|xi^2 - a| = |P - w0| -> S` at the boundary of `U`) and
locally injective (`2 xi xi' = -P'` is nonzero away from `0`, and
`xi'(0)^2 = -P''(0)/2 != 0`).  A proper local homeomorphism onto a simply
connected domain is a homeomorphism, so `Z := xi^(-1) : Qtilde -> U` is a
conformal bijection extending the local solution.  The segment `[-1,1]` lies
in `Qtilde` because `1 - xi^2` runs over `[0,1]` in `Q`; its image `Gamma` is
the canonical connector, contained in `{|P| <= 1}`, with endpoints
`Z(+-1)` in the fibre over `0`, distinct by injectivity.

**Step 3: a Möbius normal form.**  Let `M(w) = wS/(S^2 + a w - a^2)`, the
Möbius map of `D(a,S)` onto the unit disk with `M(0) = 0`.  For `w` in
`[0,1]` it is real and increasing (`M'(w) = S(S^2-a^2)/(S^2 + aw - a^2)^2 > 0`).
Then `zeta(xi) = xi sqrt(S/(S^2 + a xi^2 - a^2))` is a single-valued conformal
bijection of `Qtilde` onto the unit disk (again a proper local homeomorphism,
with `zeta^2 = M(xi^2)`), odd and increasing on `[-1,1]`, mapping it onto the
real diameter segment `[-q, q]` with

```text
q^2 = M(1) = S/(S^2 + a - a^2) = S/(S^2 + p),     p = a(1-a) = w0(1-w0).
```

**Step 4: the Bergman segment inequality.**  Put `Phi = Z o zeta^(-1) : D -> U`,
a conformal bijection, so `Phi' in A^2(D)` with
`||Phi'||^2 = Area(U)`, and `len(Gamma) = int_{-q}^{q} |Phi'(s)| ds`.  Lemma A
of `BergmanSegmentLengthBound.md` (Cauchy–Schwarz against the Bergman
kernel, positive on real pairs) gives

```text
len(Gamma)^2 <= Lambda(q) Area(U),
Lambda(q) = (2/pi) log((1 + q^2)/(1 - q^2))
          = (2/pi) log((S^2 + S + p)/(S^2 - S + p)).
```

**Step 5: area through the exterior-fibre capacity gap.**  Take any
`S' < S` and let `U'` be the component of `{|P - w0| < S'}` containing `0`.
The polynomial `g = P - w0` has degree `n` and unimodular leading
coefficient; its critical points are those of `P`, none of which lies on
`{|g| = S'}` because `|g(0)| = 1 - w0 < S'` and `|g(d_j)| >= S > S'`.  So
every `S'` in `(1 - w0, S)` is a regular value of `|g|`, `U'` is a regular
component, and it contains exactly `k = 2` zeros of `g` counted with
multiplicity (the fibre of the degree-two map `P|U'` over `w0`; a double
point at `0` when `w0 = 1`).  Since `n >= 3` the component is proper, and
Theorem 2 of `ExteriorBlaschkeFibreCapacityGap.md` (the exterior boundary
speed `n - |B'| > 0` combined with the harmonic-measure fibre identity)
gives the strict product gap

```text
cap(closure U')^n / S'  <  k/(2n - k) = 1/(n - 1).
```

Pólya's inequality `Area(K) <= pi cap(K)^2` for compact `K` (Pólya 1928)
then yields `Area(U') < pi (S'/(n-1))^(2/n)`.  Letting `S'` increase to `S`
through the (automatically regular) values, `U'` exhausts `U`, so

```text
Area(U) <= pi (S/(n-1))^(2/n).
```

Combining with Step 4 proves (DF).  The scaled statement follows by
`z = c + rho w`, which multiplies lengths by `rho` and turns `{|P| <= 1}`
into `{|f| <= |v|}`.  Corollary B is immediate from `rho <= R < 1` when
`c` is a minimising hub, or from `|f(c)| < 1` directly.  ∎

**Corollary C.**  For `4/3 <= S <= 2` and `n >= 3`, `S/(n-1) <= 1`, so the
radial factor lies in `(0,1]`; for `p >= 0`,
`(S^2+S+p)/(S^2-S+p) <= (S+1)/(S-1) <= 7`; and `log 7 < 2` because
`e^2 > 2.718^2 > 7`.  The three inequalities and the sign-free consumer
`length^2 <= 2C, C < 2 ==> length < 2` are the Lean declarations

```text
ErdosProblems.Erdos1041.diskFamilyCoefficient_lt_two_of_uniform_separation
ErdosProblems.Erdos1041.diskFamilyCoefficient_radius_two_lt_two
ErdosProblems.Erdos1041.diskFamilyCoefficient_three_six_fifths_lt_two
ErdosProblems.Erdos1041.diskFamily_length_lt_two_of_squared_bound
ErdosProblems.Erdos1041.diskFamily_length_lt_two_of_uniform_separation
```

in `DiskFamilyCriticalValueSeparation.lean`.  ∎

## 3. What changed relative to the 2026-08-30 certificate

The old argument had the same Steps 1–2 at `w0 = 1` and then lost in three
places.  Each loss is now removed by an ingredient that already existed in
this directory.

1. **Series Cauchy–Schwarz -> Bergman kernel.**  The old proof bounded
   `int |Z'|` by `2 sum |a_k|` and then by Cauchy–Schwarz against
   `sum 1/(k R^(2k))`, giving the factor `4 log(S/(S-1))`.  Lemma A gives
   `2 log((S+1)/(S-1))`, and `(S+1)/(S-1) < S^2/(S-1)^2` always.
2. **Triangle inequality on the level -> the `P - w0` lemniscate.**  The
   old proof enclosed `U` in `{|P| < 1 + S}` and used the global Pólya
   bound `pi (1+S)^(2/n)`.  But `U` is a component of the lemniscate of
   the unimodular-leading polynomial `P - w0` at level `S`, so the global
   bound is `pi S^(2/n)`.
3. **Global Pólya -> proper-component capacity gap.**  Because the
   component carries only two of the `n` zeros of `P - w0`, its capacity is
   strictly below the lemniscate capacity by the exterior-fibre factor
   `(n-1)^(-1/n)`.  This is the only place the degree enters beyond
   `S^(2/n)`, and it is why the thresholds dip below `coth(1)` in small
   degree.

Together the squared coefficient falls from `4 (1+S)^(2/n) log(S/(S-1))` to
`2 (S/(n-1))^(2/n) log((S+1)/(S-1))`; at `(n, S) = (3, 4)` that is
`3.365 -> 1.621`.  The free centre `w0` is new: it interpolates between the
branch-value disk of the old certificate (`w0 = 1`) and the critical-modulus
window of `MinimalHubWindowJoin.md` / `FirstTwoCriticalOptimizedBergman.md`
(`w0 = 0`), and it is genuinely different from both at interior centres,
since `D(1/2, S)` neither contains nor is contained in `D(0,S)` or `D(1,S)`.

Two remarks on the `w0 = 0` member.  `FirstTwoCriticalOptimizedBergman.md`
caps the observation level at `L = min(beta_2, 1)`.  The cap is unnecessary
for the canonical connector, which lies in `K_mu` regardless of the level at
which its area is estimated; Theorem A at `w0 = 0` is that theorem with the
cap removed, and the two coincide when `beta_2 <= 1`.  `MinimalHubWindowJoin.md`
is Theorem A at `w0 = 0` without the exterior-fibre factor; its thresholds
`x_n^*` tend to `coth(1) = 1.3130...`, not to `1` (the working-tree paper
draft currently says "decreases to 1" at `res:minimal-hub-window`; the exact
identity `Psi_n(coth u)^2 = 4u coth(u)^(2/n)` forces `u -> 1`).

## 4. Attribution and inputs

* Pólya's area–capacity inequality `Area(K) <= pi cap(K)^2` (Pólya 1928) is
  the only external theorem used.  It is applied to the closure of a proper
  regular lemniscate component, never to a sublevel set of a Blaschke
  product.
* The exterior-fibre capacity gap is `ExteriorBlaschkeFibreCapacityGap.md`
  Theorem 2 (this directory, 2026-08-26); its scalar kernel is
  Lean-checked there.
* The Bergman segment inequality is Lemma A of
  `BergmanSegmentLengthBound.md` (this directory), with the closed form
  `Lambda(q) = (2/pi) log((1+q^2)/(1-q^2))`.
* **Dubinin, "Some inequalities for polynomials and rational functions
  associated with lemniscates", J. Math. Sci. 193 (2013) 45–54, Theorem 1**
  was flagged by the 2026-09-02 prior-art pass (E1) as an uncited input to
  the separation argument, on the strength of Tao's 25 March 2026 comment
  ("By Theorem 1 of this paper of Dubinin (a Pólya type inequality), this
  area is at most `s^{2/m}` times the area of `U`").  Read against that
  quotation, Dubinin's Theorem 1 is the *relative* Pólya inequality: the
  area of a sublevel component of `{|P| < s}` inside a level-one component
  `U` with `m` zeros is at most `s^(2/m) Area(U)`.  That statement enters
  **neither** the 2026-08-30 separation argument **nor** the present proof:
  both use only the absolute inequality `Area(K) <= pi cap(K)^2` on a
  lemniscate component.  It **does** enter this directory at
  `actual_component_merge_tree_area_lower_bound`
  (`ActualComponentMergeTreeAreaLowerBound`, the branch monotonicity
  `A(R)/R^(2/k)` nondecreasing), which is exactly Dubinin's relative
  inequality and which the first-merge capacity closures consume; that row
  should cite Dubinin.  The full text of Dubinin's paper was not obtained in
  this session (Springer paywall; the POMI original was not located), so the
  identification rests on the quoted statement and must be confirmed against
  the paper before external submission.

No literature-priority claim is made for Theorem A.  The prior-art pass
located no published critical-value-separation criterion of this shape.

## 5. Exact residual

Theorem A fires at a simple admissible hub `c` unless **every** real centre
`w0` in `[0,1]` has some other critical value inside `D(w0, S_n^*(w0))`.
At a minimising hub every `v_j` has `|v_j| >= 1`, so the residual set for the
second critical value is the lens

```text
E_n = { w : |w| >= 1 }  ∩  ⋂_{w0 in [0,1]} D(w0, S_n^*(w0)).
```

In degree three this is the crescent `1 <= |w| < 1.109`, `|w - 1| < 1.109`,
`|w - 1/2| < 0.631`; in every degree it is contained in
`{1 <= |w| < coth(1)} ∩ {|w - 1| < coth(1)}`, i.e. the second critical value
must be within ratio `1.313` of the first in modulus **and** within angle
`arccos((1 - coth(1)^2 + |w|^2)/(2|w|))`, at most about `82` degrees, of it in
argument.  Any counterexample to Erdős 1041 with a simple minimising hub has
its second critical value in this lens.  The random sweep in the receipt
reports the theorem firing at the minimising hub on roughly four fifths of
the sampled configurations; the remaining fifth is the lens, populated
chiefly by near-Fekete and clustered configurations.

This lens is where the parent problem lives.  The extremal family
`z^n - r^n` sits at its centre (all critical values coincide), attains the
target with equality, and defeats every estimate with positive loss; so the
lens cannot be closed by any Bergman/Pólya-type inequality of the present
shape, and the next step must be exact.  The two-branch-point resolved
cover (a three-sheeted component over a disk containing both `1` and `v_2`)
is simply connected, but its uniformising coordinate places the connector at
a distance comparable to `|1 - v_2|^(1/2)` from the boundary, so the
corresponding Bergman constant diverges like `log(1/|1 - v_2|)` in the
near-tie limit.  That is the exact obstacle, not the two-sheeted cover.

## 6. Falsifier receipt

`formal_math/probes/erdos1041_disk_family_separation_probe.py` traces both
branches of the connector by integrating `dz/ds = -2s/P'(z)` from the exact
series start, evaluates (DF) at twenty-one centres with the sharpest
admissible radius, and records the worst ratio `len/bound` over every simple
hub of uniform, boundary-heavy, near-Fekete, clustered, and concyclic root
configurations in degrees three through eight, followed by an adversarial
hill-climb from the worst seed and a grid check of the exterior-fibre area
gap.  The numbers are in
`disk_family_critical_value_separation_probe_receipt.json`; a ratio above
one would falsify Theorem A and none occurred.  Replay:

```sh
./repo-python formal_math/probes/erdos1041_disk_family_separation_probe.py --degrees 3,4,5,6,7,8 --samples 120 --climb 150 --area-checks 25
```

Measurement is not proof authority; Theorem A is proved in §2.
