# Erdős 1041: joint assimilation of six returned packets

## Status

This source assimilates the six returns preserved in
`state/formal_math/type_b_return_batches/erdos1041_20260826_return_stream_01`.
Every return was read against the current Erdős 1041 corpus, including the
earlier 2026-08-26 multi-return assimilation and the optimized first-two-level
Bergman theorem.  This synthesis is current through 2026-08-27.

The unrestricted problem is not proved here.  The returns contain several
exact theorems, but their proposed endpoints stop at three versions of the
same unresolved allocation problem: selecting two sheets, one critical block,
or one attachment-compatible component without discarding the polynomial
coupling.  Two local improvements are proved below:

1. the full-forest lifetime inequality has a positive full-energy entrance
   charge at every nontrivial node, plus a singleton-leaf charge, both of which
   the return discarded from its scalar lifetime corollary;
2. the dimension-free Gram stability bound loses only one power of its
   spectral ceiling, not two.

Together with `FirstTwoCriticalOptimizedBergman.md`, this is strictly stronger
than the six packets taken separately.

The scalar authority anchors are [`fullEnergyChargedLifetimeBudget`](SixReturnJointAssimilation20260826.lean#L18-L24),
[`leafChargedLifetimeBudget`](SixReturnJointAssimilation20260826.lean#L27-L34),
[`spectralDeviation_sum_le`](SixReturnJointAssimilation20260826.lean#L47-L57),
and the conditional critical-pole consumer
[`criticalPoleTrace_charge_nonneg`](SixReturnJointAssimilation20260826.lean#L63-L74).
Replay the companion module from the repository root with:

```sh
lake env lean research_corpus/Erdos1041/SixReturnJointAssimilation20260826.lean
```

These declarations check only the scalar fan-in and conditional charge
consumers; the complex-analytic and geometric statements remain the ordinary
proofs and reconciliations recorded below.

## 1. Retained exact results

The following results survive source reconciliation.

### 1.1 Optimized separated first merge

For distinct critical moduli `0 < beta_1 < beta_2`, put

```text
L = min(beta_2, 1).
```

The first return's observation level `sqrt(beta_1 beta_2)` is suboptimal.  The
cost

```text
t^(2/n) log((t+beta_1)/(t-beta_1))
```

decreases strictly for `t>beta_1`.  Hence the exact sufficient condition is

```text
L^(2/n) (1/(n-1))^(2/n)
  log((L+beta_1)/(L-beta_1)) < 2.
```

The proof and Lean scalar kernel are in
`FirstTwoCriticalOptimizedBergman.md/.lean`.

### 1.2 Scalar comb obstruction and actual comb topology

On an abstract binary comb with node sizes `2,...,n` and common ratio
`rho_n=exp(-c/n^2)`, every immediate and ancestor ratio tends to one while

```text
product_(k=2)^n rho_n^(k-1)
  = exp(-c(n-1)/(2n)).
```

Thus rapid ratios and the topology product alone do not force discriminant
ratio tending to one.  Separately, the generic lemniscate-tree realization
theorem permits comb topology.  Affine shrinking preserves that topology while
placing the roots and critical values below the normalized target.  This does
not realize arbitrary metric labels and is not a counterexample to the target.

The returned cubic

```text
f(z)=(z^2-1)(z-a),
a=-1/1000+(9/10)i,
```

is a stronger actual-polynomial no-go for the raw ratio inference: both node
thresholds fail while its exact discriminant ratio is

```text
121337022963 / 250000000000 < 1/2.
```

### 1.3 Unicritical terminal ties

For `f(z)=(z-c)^n-alpha`, all roots lie on a circle of radius
`r=|alpha|^(1/n)`.  Root-to-centre radial segments satisfy

```text
|f(c+t(a-c))| = |alpha|(1-t^n),
```

so two roots are joined through `c` with length `2r<2` when the roots lie in
the open unit disk.  This closes the maximally coalesced terminal equality
model in every degree.

### 1.4 Full-forest lifetime and transported antichains

For an active `k`-root component born at critical modulus `beta` and observed
at level `t`, put

```text
lambda_k(beta/t)
  = log((1+(beta/t)^(2/k))/(1-(beta/t)^(2/k))).
```

If no closed root path of length at most two exists, ConnectedClusterBergman
and Pólya area give at every regular level

```text
sum_(active nontrivial C) 2/lambda_(k_C)(beta_C/t)
  < t^(2/n).
```

Integration over the disjoint log-level lifetimes of the merge nodes gives

```text
sum_v I_(k_v)(r_v) < n/4,
I_k(r)=integral_r^1 dq/(q lambda_k(q)).
```

This genuinely prices a nested chain.  The returned transported-antichain
inequality independently prices branching and is optimal among arguments that
use only node demands, branch area transport, additivity of incomparable
components, and one terminal area cap.

### 1.5 Critical-pole disk budget

For `c` in the closed disk `D(q,R)`, with `d=|c-q|`, polar integration centred
at `c` gives

```text
(1/pi) integral_(D(q,R)) dA(z)/|z-c|
  = (4R/pi) E(d^2/R^2)
  <= 2R-d^2/(2R).
```

This exact theorem is retained.  Its proposed critical-pole trace inequality

```text
length(Gamma_Omega)
  <= sum_(c in Crit(Omega))
       (1/pi) integral_(D(q,R)) dA(z)/|z-c|
```

is not proved.  Conditional on it, the corpus's combined charge closes with
the quantitative dispersion credit

```text
2R(k-1)-length(Gamma_Omega)
  >= sum_c |c-q|^2/(2R).
```

The conditional arrow must not be recorded as a proof of the target.

### 1.6 Critical-value translated truncation

Let `c` be a nonroot critical point, `mu=|f(c)|`, and let `r<=q` be the two
smallest root distances from `c`.  Reciprocal balance and the product identity
give

```text
q <= (n-1)r,
r+q <= 2 mu^(1/n).
```

The translated two-piece path

```text
c+r u  ->  c+r v  ->  c+q v
```

has length at most `2 mu^(1/n)`.  Its exact containment certificate is

```text
((r+q)^2/4) product_(j>=3)(q+d_j) <= R^n.
```

The degree-only sufficient condition is

```text
mu <= tau_n R^n,
tau_n = 2^(4-n)(n-1)/n^2.
```

Thus, on the normalized class, failure of the target implies every critical
modulus is strictly larger than `tau_n`.  The return's critical-centred
spoke-or-cut lemma would settle the problem but remains unproved; its
complex Lagrange weights do not provide the missing positive selection.

### 1.7 Angular full-fibre action

For inverse branches of

```text
P(z_j(s,theta))=s^n exp(i theta),
```

the inverse-sheet Jacobian is

```text
J_j=(s/n)|partial_s z_j|^2.
```

The area formula, integration by parts, and Pólya's bound
`Area{|P|<s^n}<=pi s^2` therefore prove

```text
(1/(2pi)) integral_theta sum_j integral_0^R
  |partial_s z_j|^2 ds dtheta <= nR.
```

For some regular angle, total integrated branch length is at most `nR`, and
the sum of the `q` shortest consistently labelled branches is at most `qR`.
In particular two branches have total length at most `2R`.

This does not yet connect their root endpoints.  A connector requires those
two branches to meet at a critical point or to be changed into one another by
monodromy.  The return's safe-block localization is exactly the missing step;
full-fibre compensation may otherwise be spent on singleton sheets outside the
selected component.

## 2. New theorem: full-energy-charged lifetime budget

The return proves the fixed-level full-FE maximum but its scalar lifetime
corollary discards both the merge-propagated energy and all singleton
components.  The maximum can be decomposed into the returned Bergman lifetime
plus an explicit positive entrance charge on every nontrivial node.

Assume the generic separated setting first.  For each root `a_i`, let
`sigma_i` be the level at which its singleton component first merges, truncated
at the target cut `1`.  Until `t=sigma_i`, branch area monotonicity for degree
one gives

```text
Area(C_i(t))/pi >= t^2/|f'(a_i)|^2.                      (LC1)
```

For an internal node `v`, let `E_v>0` be its merge-propagated leaf energy and
write `beta_v<t<delta_v` for its lifetime.  Define

```text
J_v = integral_(beta_v)^(delta_v)
  [max{t^(2/k_v) E_v,
       2/lambda_(k_v)(beta_v/t)}
   - 2/lambda_(k_v)(beta_v/t)] dt/t.                    (LC0)
```

The integrand is nonnegative.  It is strictly positive on an interval just
above `beta_v`: the Bergman demand tends to zero as `t` decreases to the birth
level, while `t^(2/k_v)E_v` tends to the positive number
`beta_v^(2/k_v)E_v`.  Hence `J_v>0` for every genuine nontrivial node.

### Theorem A — fixed-level full-energy aggregate

If no two listed roots are joined in `|f|<=1` by a path of length at most two,
then at every regular `0<t<1`,

```text
sum_(active nontrivial C)
  max{t^(2/k_C) E_C,
      2/lambda_(k_C)(beta_C/t)}
+ sum_(i: t<sigma_i) t^2/|f'(a_i)|^2
< t^(2/n).                                                (LC2)
```

#### Proof

For a nontrivial active component, the branch theorem and failure of the
Bergman path force both

```text
Area(C)/pi >= t^(2/k_C)E_C,
Area(C)/pi >  2/lambda_(k_C)(beta_C/t).
```

Thus area dominates their maximum.  For a singleton component use (LC1).
These are different components of the same sublevel set, hence their areas
add.  Pólya gives total normalized area at most `t^(2/n)`, proving (LC2).

### Corollary A1 — strict strengthened lifetime budget

Integrating (LC2) against `dt/t` yields

```text
2 sum_v I_(k_v)(r_v)
 + sum_v J_v
 + (1/2) sum_i sigma_i^2/|f'(a_i)|^2
< n/2.
```

Equivalently,

```text
boxed(
  sum_v I_(k_v)(r_v)
  + (1/2) sum_v J_v
  + (1/4) sum_i sigma_i^2/|f'(a_i)|^2
  < n/4.)                                                 (LC3)
```

Every `J_v` and every summand in the new leaf charge is positive for a
squarefree separated polynomial.  Thus (LC3) strictly strengthens the
returned lifetime budget at every actual node, not only at leaves.  Coalescing
levels follow by approximation; repeated roots already give the target by a
constant path.

The extra terms are structurally aligned with the long-comb residual: every
newborn component pays a positive energy-dominant interval before its Bergman
demand takes over, and a root which remains singleton through earlier mergers
also pays up to its attachment level.  Whether (LC3), the transported-antichain
constraints, and the merge product jointly force a target-deciding node is a
new finite optimization problem.  No such forcing theorem is claimed here.

## 3. New theorem: sharper dimension-free Gram stability

Retain the return's normalized Vandermonde row-Gram matrix `H`, with positive
eigenvalues `lambda_i`, trace `n`, determinant at least `delta`, and

```text
M_delta exp(1-M_delta)=delta,
M_delta>=1.
```

The return proves `lambda_i<=M_delta` but uses the coarse second-derivative
bound

```text
x-1-log x >= (x-1)^2/(2 M_delta^2).
```

Only one power of `M_delta` is necessary.

### Lemma B — sharp one-ceiling convexity bound

For `M>=1` and `0<x<=M`,

```text
x-1-log x >= (x-1)^2/(2M).                            (GS1)
```

#### Proof

If `0<x<=1`, put

```text
g_-(x)=x-1-log x-(x-1)^2/2.
```

Then `g_-(1)=0` and

```text
g_-'(x)=-(x-1)^2/x <=0.
```

Hence `g_-(x)>=0` to the left of one, and division by `M>=1` only weakens the
quadratic term.

If `1<=x<=M`, put

```text
g_+(x)=x-1-log x-(x-1)^2/(2x).
```

Then `g_+(1)=0` and

```text
g_+'(x)=(x-1)^2/(2x^2)>=0.
```

Thus `x-1-log x >=(x-1)^2/(2x)>=(x-1)^2/(2M)`.

### Theorem B1 — improved spectral defect

Since `sum_i(lambda_i-1)=0`,

```text
sum_i [lambda_i-1-log lambda_i]
  = -log det H
  <= log(1/delta).
```

Applying (GS1) gives

```text
boxed(
  ||H-I||_F^2
    <= 2 M_delta log(1/delta).)                           (GS2)
```

This strictly improves the returned
`2 M_delta^2 log(1/delta)` bound whenever `delta<1`, without adding a factor
depending on the degree.  Consequently the number of rows with squared
off-diagonal coherence at least `eta` is at most

```text
2 M_delta log(1/delta)/eta.
```

The exact radial-angular determinant factorization and the return's radial
deficit estimate remain valid.  The improved Gram theorem still does not by
itself select a connector stable under the bounded defect set.

## 4. Joint target-facing consequence

For a normalized squarefree polynomial which evades every theorem now landed,
all of the following must hold simultaneously:

1. every critical modulus exceeds `tau_n` (translated-cut failure);
2. the optimized first ratio
   `beta_1/min(beta_2,1)` fails the direct Bergman threshold;
3. every actual merge node fails its fibre-capacity Bergman threshold;
4. the full-energy-charged lifetime budget (LC3) holds;
5. every transported-antichain inequality holds;
6. the merge-tree critical product obeys the topology-dependent floor;
7. whenever that floor gives `D>=delta`, the sharper radial-angular estimates
   and (GS2) apply;
8. full-fibre angular action has two short branches, but no proved theorem
   places them in one trace-selected monodromy block.

This is a strictly smaller residual than any returned packet records.  It is
not empty by any theorem currently in the corpus.

## 5. Why the five new returns do not yet compose to a full proof

The three most promising proposed endpoints have the same missing quantifier
in different coordinates.

| Coordinate | What is proved | Missing allocation |
|---|---|---|
| critical forest | total pole budget in the enclosing disk | a cut-surface calibration with sharp `1/pi` mass |
| critical-centred finite templates | sharp length and containment certificates | one pair/template satisfying containment at the same critical point |
| angular inverse fibres | two globally short integrated branches | the two branches lie in one safe monodromy block |

The lifetime and antichain theorems constrain how often these failures can be
reused across the merge forest, while the Gram theorem constrains the hard
discriminant branch.  None currently supplies the missing allocation.

The next target-deciding mathematical move should therefore couple the new
leaf charge to one of the root-indexed consumers already present in the corpus,
rather than add another scalar product or terminal area inequality.

## 6. Claim boundary

Proved here by ordinary mathematics: (LC0)--(LC3), (GS1), and (GS2), together
with the exact reconciliation of the six returns.

Lean-checked in the companion module: the full-energy and leaf-charge fan-in,
its strict improvement over the uncharged budget, the dimension-free spectral
fan-in, and the conditional critical-pole dispersion consumer.

Retained as exact ordinary results from the returns: the comb scalar no-go,
unicritical closure, radial-angular determinant factorization, lifetime and
transported-antichain inequalities, cubic ratio no-go, disk pole budget,
critical-value translated-cut theorem, and angular full-fibre action theorem.

Still unproved: critical-pole trace calibration, critical-centred spoke-or-cut,
safe-block action localization, a target-deciding consequence of (LC3),
componentwise combined charge, COVER, FP--GM, and unrestricted Erdős 1041.
