# Erdős 1041: finite-capacity continuation and the first-contact obstruction

## Status

The complete three-exterior selector is now proved on a positive
low-capacity interval.  This note identifies exactly what can stop that
interval from continuing through the full speed-admissible range.

On every compact capacity subinterval below saturation, the proved set is
open as long as regular triangles are the only equality configurations, and
it is closed for strict-speed configurations.  Therefore a first failure can
occur only through a **nonregular equality contact** (possibly on the closed
speed boundary).  If no such interior contact exists, the only remaining
escape is accumulation at the saturation endpoint, where the regular
optimizer reaches the unit circle and the present local Hessian theorem
degenerates.

This is an exact continuation reduction, not a proof that the obstruction is
absent.  A deterministic numerical falsifier finds no nonregular contact; its
tightest cells are the final near-saturation slabs.  Those computations are
not certificates.

## 1. Capacity-indexed compact problem

Fix `n in {5,6}`, put `d=n-3`, and write

```text
p_0=d/(n+3),                0<p<p_0,                   (1)
s=p^(1/3).
```

For product-one normalized radii `b_0b_1b_2=1`, let `K_n(p)` be the compact
radial/angle region

```text
T_n^(-2)<=b_j<=T_n,          |a_j|=s b_j<=1,           (2)
```

with the closed boundary-speed condition `max_T |B'|<=n`.  Let `V_j` be the
optimized attached-ray barrier and `R_n(p)` the regular comparator.  Define

```text
Phi_n(p,C)=min_j log(V_j(C)/R_n(p)).                    (3)
```

The desired strict-speed theorem at capacity `p` is

```text
Phi_n(p,C)<=0 for every C with max_T |B'|<n.            (4)
```

Each `V_j` is a maximum of a continuous function on a compact ray interval,
so it is continuous in the configuration.  The same is true of `R_n(p)`.
Thus `Phi_n` is continuous.  The finite imbalance theorem already handles
the complement of (2); no continuation issue is hidden at radial infinity.

## 2. Openness under equality rigidity

> **Proposition 1.**  Suppose (4) holds at `p=p_*`, and every equality
> configuration at that capacity is a regular triangle.  Then (4) holds for
> all capacities in a neighborhood of `p_*`.

### Proof

The finite regular mixed-kernel theorem gives an attachment-compatible
neighborhood of the regular orbit in which (4) holds, and its strict first-
and second-order inequalities persist for nearby `p` because `p_*` is below
the saturation endpoint.  On the compact complement of that neighborhood,
equality rigidity makes `Phi_n` strictly negative.  Its maximum there is a
negative number, which remains negative for nearby capacities by uniform
continuity.  The two regions cover `K_n(p)` after a harmless enlargement of
the regular neighborhood.  ∎

The regular local theorem is used here in its full finite form.  A
homogeneous collar is not enough away from zero capacity.

## 3. Closedness and first contact

> **Proposition 2.**  The set of capacities for which (4) holds is closed
> with respect to strict-speed test configurations.

### Proof

Let `p_k->p` through proved capacities and fix a configuration at `p` with
strict speed.  Scaling its three radii to product `p_k` produces nearby
configurations which still have strict speed.  Continuity of (3) and (4) at
`p_k`, followed by `k->infinity`, gives (4) at `p`.  ∎

The uniform finite equality collar proves a nonempty initial interval.  If
the selector fails at some capacity below `p_0`, let `p_c` be the infimum of
the failing capacities.  Propositions 1--2 imply:

> **First-contact alternative.**  At `p_c` there is a nonregular
> configuration in the closed compact region (2) satisfying
>
> ```text
> Phi_n(p_c,C)=0.                                       (5)
> ```
>
> It either has strict speed, or lies on the boundary `max_T|B'|=n` as the
> limit of strict-speed configurations.

If the contact is interior to all constraints, nonsmooth first-order
optimality for the local maximum of the minimum gives nonnegative weights
`lambda_j`, supported on the active equality rays and summing to one, such
that

```text
sum_j lambda_j D_C log V_j=0                           (6)
```

on the fixed-product angle/radius tangent space.  Each active ray optimizer
also satisfies its one-variable stationarity equation.  Thus an interior
first contact is a finite algebraic/KKT system, not an arbitrary five-
variable inequality point.

Equation (6), a speed-boundary contact, and endpoint saturation are the exact
three cells a complete continuation proof must exclude.

## 4. Why saturation remains separate

The saturation-rigidity theorem says that equality `p=p_0` under the closed
speed condition forces the regular finite Blaschke product.  This prevents a
different endpoint equality object, but it does not give a quantitative rate
at which near-saturating configurations approach the regular orbit.

At `p=p_0`, the regular optimized barrier equals its unit-circle endpoint
value one.  Simultaneously the strict interior-ray Hessian calculation in
`ThreeExteriorFiniteRegularMixedKernelStability.md` degenerates.  Therefore
qualitative saturation rigidity alone cannot provide a uniform terminal
collar.  A proof needs either

```text
distance(configuration,regular)^2
 <= constant*(p_0-p)                                  (7)
```

from the boundary-speed defect, or a direct endpoint-scaled selector atlas.
This is the sharp current friction, not loss of compactness.

## 5. Coarse falsifier map

The accompanying deterministic probe samples product-one radial shapes and
two genuine angles, rejects configurations violating strict speed, optimizes
all three attached rays, and records `min_j V_j/R_n(p)`.  With 600 attempted
samples at each of nine capacity scales per degree, it found no ratio above
one.

Away from a `0.10` normalized distance from the regular orbit, the tightest
observed rows were

```text
n=5: s=0.611061709, ratio=0.984749240,
n=6: s=0.672560436, ratio=0.984231082.                 (8)
```

Both lie in the last sampled slabs before

```text
n=5: s_0=(1/4)^(1/3)=0.629960...,
n=6: s_0=(1/3)^(1/3)=0.693361....                     (9)
```

The number of randomly generated strict-speed configurations also collapses
in those slabs.  The probe therefore points to the saturation defect in (7),
not to an interior candidate counterexample.  It cannot exclude a thin KKT
contact and is not used in Propositions 1--2.

## Replay

```sh
./repo-python formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1041/scripts/probe_erdos1041_three_exterior_finite_capacity_continuation.py --samples 600
```

## Exact boundary

The low-capacity interval is proved.  Extension to all `0<p<p_0` is reduced
to excluding nonregular contacts (5)--(6), including contacts on the closed
speed boundary.  If those are excluded on compact interior capacity
intervals, the sole residual is a quantitative saturation collar proving
(7) or an equivalent endpoint selector estimate.  No all-capacity theorem is
claimed here.

```text
tao_pipeline_receipt:
  input_stage: complete low-capacity finite selector
  output_stage: open-closed continuation and exact first-contact reduction
  artifact: ThreeExteriorFiniteCapacityContinuationReduction.md plus deterministic numerical falsifier
  human_understanding_delta: continuation can fail only by a nonregular equality/KKT contact or by loss of quantitative control at speed saturation
  verification_state: ordinary compactness/continuation proof; numerical map is computational evidence only
  publication_or_review_state: source-level research result, not independently reviewed
  canonicalization_state: continuation reduction in the finite adaptive-minray family
  unresolved_downstream_bottleneck: exclude nonregular finite contacts or prove a quantitative saturation-defect collar
  next_stage_owner: finite compact KKT atlas or speed-saturation stability lane

paper_assimilation:
  paper: erdos-1041-lemniscate-newton-flow
  section: exterior finite-Blaschke adaptive selector
  canonical_mechanism_family: low_capacity_adaptive_minray
  relation: continuation reduction beyond the proved low-capacity producer, not parent closure
  understanding_delta: the remaining finite-capacity problem has a first-contact algebraic system and a separate endpoint-rate obstruction
  evidence_boundary: exact topological reduction plus non-rigorous coarse probe
  hard_step: openness from finite regular equality rigidity and closedness under strict-speed scaling
  meaningful_failed_route: saturation rigidity without a defect rate does not furnish the terminal uniform collar
  open_remainder: finite KKT contact exclusion and quantitative saturation stability
```
