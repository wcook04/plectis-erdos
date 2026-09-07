# Erdős 1041: a uniform finite equality collar by kernel continuation

## Status

This note closes the finite equality collar left by
`ThreeExteriorFiniteLowCapacityQuantitativeLift.md`, at a non-explicit but
strictly positive capacity scale.  It composes three proved inputs:

1. the exact homogeneous `1/50` selector collar;
2. the full finite regular mixed-kernel stability theorem;
3. analyticity of the normalized finite Blaschke barriers at zero capacity.

The result is a uniform collar, not a separate pointwise neighborhood for
each positive capacity.  Combined with the explicit off-collar lift and the
finite imbalance cone, it proves the complete three-exterior adaptive-ray
selector theorem for all sufficiently small capacities in degrees five and
six.

The threshold obtained by compactness is not numerical.  This closes the
low-capacity selector regime, not all capacities and not Erdős #1041.

## 1. Analytic normalized family

Let

```text
a_k=epsilon b_k u_k,        b_0b_1b_2=1,
```

and use reciprocal ray coordinate `q`, so the physical point is
`epsilon u_j/q`.  Put `e=epsilon^2`.  The normalized squared ray barrier is

```text
F_j(e,q,b,c)
 =q^(2n) product_k(1-2qb_kc_jk+q^2b_k^2)
  /product_k(q^2-2e q b_kc_jk+e^2b_k^2).              (1)
```

On the `1/50` radial/angular/ray chart, and for
`0<=epsilon<=10^(-6)`, every denominator in (1) is bounded below by

```text
(q-e b_k)^2>49/100.                                   (2)
```

Thus (1), all of its configuration derivatives, and its `q` derivatives are
uniformly analytic on a neighborhood of the closed chart.

For the regular triangle the finite optimizing reciprocal radius is also
analytic at zero.  If

```text
Q=q^3,                  E=epsilon^6,
```

its stationary equation is

```text
nQ^2-[d+(n+3)E]Q+nE=0,       d=n-3.                  (3)
```

At `(Q,E)=(d/n,0)`, the derivative of the left side with respect to `Q` is
exactly `d>0`.  The implicit-function theorem therefore gives an analytic
regular optimizer through the homogeneous endpoint.  Optimizing (1) near
that simple critical point produces three analytic normalized log barriers

```text
g_j(e,v)=log V_j(e,v)-log R_n(epsilon^3),              (4)
```

where `v=0` is the regular product-one triangle and `g_j(e,0)=0`.

## 2. A robust min-kernel lemma

We use the following elementary finite-dimensional continuation principle.

> **Lemma.**  Let `g_0,g_1,g_2` be a `C^3` family as in (4), with parameter
> `e` in a neighborhood of zero.  Suppose at every regular centre:
>
> 1. the three first variations sum to zero;
> 2. away from their simultaneous kernel, at least one first variation is
>    strictly negative;
> 3. on the simultaneous kernel, the sum of the three Hessians is strictly
>    negative definite.
>
> If these properties hold at `e=0` and their defining jets vary
> continuously, then there are `e_0,r_0>0`, independent of `e`, such that
>
> ```text
> min_j g_j(e,v)<=0             (0<=e<=e_0, |v|<=r_0), (5)
> ```
>
> with equality only at `v=0`.

### Proof

Let `K_e` be the simultaneous first-order kernel.  Continuity and compactness
of the unit sphere give constants `sigma,kappa>0` such that, for small `e`,

```text
min_j Dg_j(e,0)[v] <= -sigma dist(v,K_e),              (6)

sum_j D^2g_j(e,0)[w,w] <= -kappa |w|^2    (w in K_e). (7)
```

All first three derivatives are uniformly bounded.  Split a small nonzero
`v` into two cases.  If

```text
dist(v,K_e)>=A|v|^2,
```

then (6), with `A` larger than the uniform quadratic remainder constant,
makes one `g_j(e,v)` negative.  Otherwise `v` differs from a vector in `K_e`
by `O(|v|^2)`.  Summing the three Taylor expansions cancels the linear term;
(7) gives `-kappa|v|^2/2`, while the kernel-approximation and cubic errors are
`O(|v|^3)`.  Their sum is negative for sufficiently small `|v|`, so again at
least one `g_j` is negative.  All constants are uniform in `e`, proving
(5).  ∎

This two-scale split is essential: a pointwise strict Hessian statement alone
does not automatically provide a uniform collar.

## 3. Verification of the continuation hypotheses

At `e=0`, hypotheses 1--3 are exactly the first-order selector decomposition
and strict kernel calculation in
`ThreeExteriorLowCapacityRegularKernelSecondVariation.md`; the quantitative
`1/50` theorem gives a closed analytic chart around it.

For positive capacity, the first-order simultaneous kernel is

```text
y_01=K(q,s)x_2,   y_02=K(q,s)x_1,   y_12=K(q,s)x_0,   (8)
```

with `K(q,s)` from
`ThreeExteriorFiniteRegularMixedKernelStability.md`.  In scaled variables
`q=sz`, its exact endpoint limit is

```text
lim_(s->0) K(sz,s)=3(z+1)/(2(z-1))
                  =3(1+t)/(2(1-t)),    t=1/z,         (9)
```

which is precisely the homogeneous kernel coefficient.  Hence the kernels
vary continuously through zero capacity.

The finite mixed-kernel theorem proves strict negativity of the summed
optimized Hessian on (8) throughout the positive speed-admissible regular
arc.  Formula (1), the simple optimizer (3), and (2) show that this Hessian
converges to the homogeneous one at `e=0`.  Its least negative eigenvalue is
therefore bounded away from zero on a sufficiently short closed capacity
interval.  The same continuity gives the transverse constant in (6).
All hypotheses of the lemma hold.

## 4. Filling the whole `1/50` collar

The lemma first supplies a uniform inner radius `r_0`.  Consider the closed
annulus inside the old collar,

```text
r_0<=|v|,       0<=M,U,V<=1/50,       |X|,|Y|,|Z|<=1/50. (10)
```

At zero capacity, the exact homogeneous collar has strict gap on (10): its
monotonicity derivatives are positive and its kernel gap is strictly convex,
with the regular point as the unique zero.  Compactness gives a positive
minimum gap on (10).  Uniform convergence of (1) and of the regular
comparator then preserves that gap for `0<=e<=e_1`, after decreasing `e_1`
if necessary.  Together with the inner lemma, this covers the entire
`1/50` collar.

## 5. Uniform finite-collar theorem

> **Theorem.**  For `n=5,6`, there exists
>
> ```text
> 0<epsilon_*<=10^(-6)                                  (11)
> ```
>
> such that every speed-admissible three-exterior configuration in the
> compact normalized radial region and in the exact `1/50` equality collar
> has an actual root-attached ray satisfying
>
> ```text
> V_j<=R_n(epsilon^3).                                  (12)
> ```
>
> Equality occurs only for the finite regular triangle.

Combining (12) with `ThreeExteriorFiniteLowCapacityQuantitativeLift.md`
closes the entire compact normalized region for `epsilon<=epsilon_*`.
Combining once more with
`ThreeExteriorFiniteImbalanceWaterFillingCone.md` gives:

> **Corollary.**  The full finite three-exterior adaptive-ray selector
> theorem holds in degrees five and six for every sufficiently small positive
> capacity.

## Replay and exact boundary

```sh
./repo-python formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1041/scripts/check_erdos1041_three_exterior_finite_uniform_equality_collar.py
```

The replay checks the stationary simple-root identity (3), the kernel limit
(9), the uniform denominator margin (2), and the speed-admissible endpoint.
The existence of `epsilon_*` is an ordinary compactness/continuation proof;
the checker does not pretend to output a numerical value.

```text
tao_pipeline_receipt:
  input_stage: explicit off-collar finite lift plus pointwise finite regular stability
  output_stage: uniform finite equality collar and complete low-capacity selector
  artifact: ThreeExteriorFiniteUniformEqualityCollar.md plus exact endpoint checker
  human_understanding_delta: transverse switching and kernel curvature persist jointly through zero capacity; a two-scale Taylor split turns pointwise regular stability into one uniform collar
  verification_state: ordinary analytic continuation/compactness proof with exact symbolic endpoint replay
  publication_or_review_state: source-level research result, not independently reviewed
  canonicalization_state: low-capacity finite selector closure in the adaptive-minray family
  unresolved_downstream_bottleneck: capacities above epsilon_* in the compact normalized region
  next_stage_owner: finite compact continuation or alternative global selector lane

paper_assimilation:
  paper: erdos-1041-lemniscate-newton-flow
  section: exterior finite-Blaschke adaptive selector
  canonical_mechanism_family: low_capacity_adaptive_minray
  relation: completes the finite low-capacity three-exterior producer, not the unrestricted parent
  understanding_delta: the homogeneous theorem is not merely asymptotic; after exact kernel continuation it controls an actual positive-capacity interval
  evidence_boundary: n=5,6 and some non-explicit epsilon_*>0; no claim for the remaining compact positive-capacity interval
  hard_step: uniform two-scale min-kernel continuation through the degenerate zero-capacity chart
  meaningful_failed_route: pointwise collars alone do not globalize without the transverse-versus-kernel quantitative split
  open_remainder: extend the finite compact selector from low capacity to the full speed-admissible interval
```
