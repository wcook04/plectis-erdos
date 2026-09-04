# Erdős 1041: an exact no-go for the finite radius-weighted ray product

## Status

The radius-weighted geometric-mean experiment for three finite exterior
Blaschke rays is **false**, even inside the strict finite admissibility
condition.  This is a single exact degree-five obstruction to that proposed
selector invariant.  It does not affect the homogeneous low-capacity
reduction, whose scaling is a different statement.

## The proposed finite invariant

For three points `a_j=r_j u_j` in the disk and an ambient degree `n`, write

```text
E_j(q)=q^(-n) product_k |(q u_j-a_k)/(1-q conjugate(a_k)u_j)|,
                     r_j<q<1,
V_j=sup E_j(q).
```

The numerical candidate was the radius-weighted comparison

```text
product_j V_j^(r_j) <= R_n(p)^(sum_j r_j),
             p=product_j r_j,                            (1)
```

where `R_n(p)` is the optimized barrier for the regular three-point factor
`(q^3-p)/(1-pq^3)`.  If (1) held, some ray would automatically meet its
regular comparator.  It does not.

## Exact symmetric specimen

Take `n=5`,

```text
r_0=r_2=59/100,       r_1=11/25,
u_1=1,                u_0=exp(-i theta), u_2=exp(i theta),
cos(theta)=-57/100.                                      (2)
```

This is strictly admissible for the finite three-point speed condition

```text
sup_phi sum_j (1-r_j^2)/(1+r_j^2-2 r_j cos(phi-arg u_j)) < 5.  (3)
```

In fact the exact checker proves the stronger rational bound `<=19/4`.
It reduces (3), with `x=cos(phi)`, to one rational function.  Its numerator
after subtraction from `19/4` has no root in `[-1,1]` and is positive at
zero; both denominators are strictly positive there.

At the centre ray, evaluate at the rational point `q=7/12`.  The value is

```text
E_1(7/12)=16651505000448/8153887797433.                  (4)
```

The regular product is `p=38291/250000`.  Exact Sturm counting shows

```text
R_5(p) < 1213/1000.                                      (5)
```

Indeed, after clearing its positive denominator, (5) is an eighth-degree
polynomial with no zero in `(0,1)` and positive value at zero.  The two
outer ray barriers have `V_0,V_2>=1`, since their limiting value as
`q` tends to one is one.  Since the radii in (2), multiplied by one hundred,
are `(59,44,59)`, exact integer comparison gives

```text
E_1(7/12)^44 > (1213/1000)^162.
```

Together with (4)--(5), this implies

```text
V_0^(59/100) V_1^(44/100) V_2^(59/100)
     > R_5(p)^(162/100),
```

contradicting (1).

## Consequence

The attractive finite-capacity extension of the homogeneous weighted-product
heuristic fails at a genuine strict-admissibility specimen, not merely at a
boundary artefact.  The failure mechanism is saturation: two rays can have
only their endpoint value one while the middle ray is expensive.  Any finite
selector theorem needs an additional speed-saturation branch (or a different
weight/invariant).  The homogeneous `m=3` adaptive-min-ray theorem remains
open only on its compact near-equal core; this no-go neither proves nor
refutes it.

## Exact replay

```sh
./repo-python formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1041/scripts/check_erdos1041_three_exterior_finite_weighted_product_nogo.py
```

```text
tao_pipeline_receipt:
  input_stage: falsification
  output_stage: exact_obstruction
  artifact: ThreeExteriorFiniteWeightedProductNoGo.md plus exact checker
  human_understanding_delta: finite weighted geometric means cannot bypass adaptive selection; near speed saturation produces two endpoint-only rays and one costly middle ray
  verification_state: exact rational arithmetic and Sturm root counts
  publication_or_review_state: source-level research obstruction, not independently reviewed
  canonicalization_state: one finite weighted-product no-go in the adaptive-selector family
  unresolved_downstream_bottleneck: find a speed-saturation splice or a genuinely adaptive finite selector
```
