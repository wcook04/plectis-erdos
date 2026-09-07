# Erdős 1041: explicit finite-capacity lift off the regular equality collar

## Status

The complete compact homogeneous three-exterior certificate has a uniform
strict rational margin outside its exact `1/50` double-active equality
collar.  This note spends that margin to obtain a genuine finite Blaschke
selector theorem whenever the common capacity scale satisfies

```text
0<epsilon<=10^(-6).                                    (1)
```

Together with the finite imbalance-cone theorem, this leaves only the finite
regular equality collar at low capacity.  No limiting argument is used on
the region proved here.

The collar itself is deliberately excluded.  Its regular centre is covered
pointwise by `ThreeExteriorFiniteRegularMixedKernelStability.md`, but a
single explicit finite collar uniform down to zero capacity is not proved in
this note.  Erdős #1041 therefore remains open.

## 1. Finite and homogeneous normalized rays

Write the three finite zeros as

```text
a_k=epsilon b_k u_k,             b_0b_1b_2=1,
```

and put `d=n-3`.  On the physical ray `z=(epsilon/q)u_j`, the normalized
finite barrier is

```text
epsilon^d E_j(epsilon/q).
```

For one zero, direct substitution gives

```text
|epsilon u_j/q-epsilon b_k u_k|^2
 =epsilon^2 q^(-2)(1-2qb_k c_jk+q^2b_k^2),            (2)

|1-epsilon^2 b_k conjugate(u_k)u_j/q|^2
 =q^(-2)(q^2-2epsilon^2qb_k c_jk+epsilon^4b_k^2).     (3)
```

Consequently

```text
[epsilon^d E_j(epsilon/q)]^2
 =q^(2n) product_k(1-2qb_kc_jk+q^2b_k^2)
   /product_k(q^2-2epsilon^2qb_kc_jk+epsilon^4b_k^2). (4)
```

At `epsilon=0`, (4) is exactly the squared homogeneous profile.

For the regular triangle, evaluating its finite comparator at the old
homogeneous maximizer `t^3=d/n` gives

```text
epsilon^d R_n(epsilon^3)
 >= C_n/(1-epsilon^6/t^3) > C_n.                       (5)
```

Thus it is enough to bound the selected finite ray by `C_n`; there is no
need to enclose the displaced finite regular maximizer.

## 2. Uniform strict margin from the exact atlas

The vertex and active-line checkers now retain the worst exact rational leaf
ratio.  Replaying every candidate tree proves, outside the `1/50`
double-active collar,

```text
H_j(q)^2 < rho C_n^2,
rho=99999999/100000000.                                (6)
```

This includes all vertical and horizontal cells, both interior stationary
profiles, all four upper-cosine clips, and the double-active Bernstein tree.
The latter is converted to a ratio by dividing its positive cleared-gap
coefficient by an adversarial rational upper bound for the clearing factor.
Hence (6) is one uniform exact number, not an inference from printed decimal
diagnostics.

## 3. Main reciprocal-radius range

Use the enlarged compact radial ceilings

```text
n=5: b_k<=29/25,              n=6: b_k<=11/10,         (7)
```

and first suppose `q>=1/4`.  From (3),

```text
|1-epsilon^2b_k conjugate(u_k)u_j/q|
 >=1-epsilon^2 T/(1/4),                                (8)
```

where `T` is the appropriate bound in (7).  Therefore (4) and (6) give

```text
[epsilon^d E_j(epsilon/q)]^2
 <=rho C_n^2/[1-4epsilon^2T]^6.                        (9)
```

For `epsilon<=10^(-6)`, exact rational arithmetic proves

```text
[1-4epsilon^2T]^6 > rho                               (10)
```

in both degrees.  Equations (9)--(10) give the desired strict bound by
`C_n^2`.

## 4. The physical endpoint tail

The remaining physical ray segment is

```text
epsilon<=q<=1/4.                                       (11)
```

The triangle and reverse-triangle inequalities give the angle-free estimate

```text
epsilon^d E_j(epsilon/q)
 <=q^d (1+qT)^3/(1-epsilon T)^3.                       (12)
```

The right side increases with `q`, so its maximum occurs at `1/4`.  The
checker proves exactly that

```text
[(1/4)^d(1+T/4)^3/(1-10^(-6)T)^3]^2<C_n^2             (13)
```

for `n=5,6`, using the same rational enclosures for `t`.  This closes the
tail all the way to the physical unit-circle endpoint.

## 5. Quantitative lift theorem

> **Theorem.**  Let `n=5` or `n=6`, let
> `a_k=epsilon b_k u_k` with `b_0b_1b_2=1`, and suppose (1) and the compact
> bounds (7).  Select the root-attached ray prescribed by the homogeneous
> first-variation selector.  If the normalized data and reciprocal ray
> parameter do not lie in the exact `1/50` double-active equality collar,
> then
>
> ```text
> E_j <= R_n(epsilon^3).                               (14)
> ```

### Proof

For `q>=1/4`, use (6)--(10).  For (11), use (12)--(13).  In both cases the
normalized finite ray is at most `C_n`, while (5) says the normalized regular
comparator is strictly larger than `C_n`.  This proves (14).  ∎

Combined with `ThreeExteriorFiniteImbalanceWaterFillingCone.md`, the theorem
removes every low-capacity three-exterior configuration except the explicit
finite equality collar.  The surviving problem is local and finite rather
than a compact five-variable global atlas.

## Replay

The two source atlases first verify the uniform ratio (6):

```sh
./repo-python formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1041/scripts/check_erdos1041_three_exterior_homogeneous_compact_relaxed_cosine.py
./repo-python formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1041/scripts/check_erdos1041_three_exterior_homogeneous_active_line_compact.py
```

Then replay the finite perturbation and tail arithmetic:

```sh
./repo-python formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1041/scripts/check_erdos1041_three_exterior_finite_low_capacity_quantitative_lift.py
```

```text
tao_pipeline_receipt:
  input_stage: complete compact homogeneous selector certificate
  output_stage: explicit finite-capacity lift outside the regular collar
  artifact: ThreeExteriorFiniteLowCapacityQuantitativeLift.md plus exact scaling/tail checker and strict-margin atlas upgrades
  human_understanding_delta: the finite denominators cost only a universal multiplicative factor away from the physical endpoint, while the endpoint tail is angle-free; the only low-capacity remainder is the regular equality collar
  verification_state: ordinary exact proof with rational atlas margins and symbolic/rational finite replay
  publication_or_review_state: source-level research result, not independently reviewed
  canonicalization_state: finite perturbative consumer of the low-capacity adaptive-minray family
  unresolved_downstream_bottleneck: explicit finite regular collar uniform for 0<epsilon<=10^-6
  next_stage_owner: finite regular mixed-kernel quantitative collar lane

paper_assimilation:
  paper: erdos-1041-lemniscate-newton-flow
  section: exterior finite-Blaschke adaptive selector
  canonical_mechanism_family: low_capacity_adaptive_minray
  relation: explicit finite lift of the homogeneous compact theorem away from equality, not parent closure
  understanding_delta: compact homogeneous strictness survives finite capacity with a concrete scale; only local equality geometry remains
  evidence_boundary: degrees five and six, epsilon<=10^-6, outside the exact 1/50 double-active collar
  hard_step: extract a single rational atlas margin and pay every finite denominator plus the endpoint tail
  meaningful_failed_route: a radius-weighted finite product invariant is false, but direct multiplicative perturbation succeeds off equality
  open_remainder: quantitative finite regular collar and subsequent parent propagation
```
