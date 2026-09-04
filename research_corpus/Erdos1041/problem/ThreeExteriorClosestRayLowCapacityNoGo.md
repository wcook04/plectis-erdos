# Erdős 1041: the closest-root ray fails arbitrarily deep in the low-capacity limit

## Status

This note gives an exact one-parameter family of degree-three exterior
Blaschke products.  For both ambient degrees `n=5` and `n=6` (moved degrees
`d=n-3=2,3`), the radial attachment barrier of the **largest-modulus
Blaschke zero** is strictly larger than the regular-triangle comparator with
the same zero product.  The failure holds for every

```text
0 < epsilon <= 1/600,
```

so it persists all the way to zero capacity.

Thus the closest excluded root cannot be the universal selector, even away
from capacity saturation.  This does not refute the optimized three-ray
envelope: one of the other two actual rays can still be cheaper.  The theorem
is an exact no-go for a selector, not a counterexample to the exterior
mountain-pass conjecture or to Erdős 1041.

## 1. A rational angular family

Let the three rational unit vectors be

```text
u_0=(1,0),
u_1=(21/221,-220/221),
u_2=(-91/109,60/109),
```

and put

```text
b_0=1,       b_1=24/25,       b_2=51/50,
P=b_0 b_1 b_2=612/625.
```

For `0<epsilon<=1/600`, define

```text
a_j=epsilon b_j u_j
```

and let `B_epsilon` be the finite Blaschke product with these three zeros.
The zero `a_2` has strictly largest modulus, so its reciprocal exterior zero
is the closest excluded root in the radial coordinate.  The zero product is

```text
p=product_j |a_j|=epsilon^3 P.                          (1)
```

The family is strictly admissible already for `n=5`.  Indeed, on the unit
circle,

```text
|B_epsilon'(zeta)|
 =sum_j (1-|a_j|^2)/|zeta-a_j|^2
 <=sum_j (1+epsilon b_j)/(1-epsilon b_j)
 <=sum_j (1+b_j/600)/(1-b_j/600)
 <5.                                                     (2)
```

Every comparison in (2) is strict except the harmless parameter endpoint,
and the final inequality is exact rational arithmetic.  Hence the same
family is admissible for `n=6` as well.

## 2. The closest-root ray has a uniform lower bound

Use the inverse-disc coordinate `q=1/x`.  On the actual ray attached to
`a_2`, evaluate at

```text
q=epsilon y,       y=4/3.                               (3)
```

This is on the geometric attachment segment because `y>b_2`.  For ambient
degree `n`, inversion gives the normalized exterior profile

```text
G_n(q)=q^(-n)|B_epsilon(q u_2)|.
```

Writing the vectors as complex numbers and using
`|1-z|<=1+|z|`, one obtains

```text
G_n(epsilon y)
 >= epsilon^(3-n) A_n / D(epsilon),                    (4)

A_n^2=y^(-2n) product_k |y u_2-b_k u_k|^2,
D(epsilon)=product_k (1+epsilon^2 y b_k).
```

All quantities in (4) are explicit.  In particular

```text
product_k |y u_2-b_k u_k|^2
 =1581501847748564/747709386328125.                    (5)
```

Since `D(epsilon)` increases with `epsilon`, (4) is uniformly bounded below
by replacing `D(epsilon)` with `D(1/600)`.

## 3. A global upper bound for the regular comparator

The regular-triangle product with the same product `p` has interior radial
profile

```text
S_n(q)=q^(-n)(q^3-p)/(1-pq^3).
```

For `0<q<=1`,

```text
S_n(q) <= (1-p)^(-1) q^(-n)(q^3-p).                    (6)
```

Put `d=n-3`.  Maximizing the last two factors over all positive `q` gives

```text
max_(q>0) q^(-n)(q^3-p)
 =epsilon^(-d) C_n,

C_n=(3/d)(d/n)^(n/3) P^(-d/3).                         (7)
```

Therefore the complete regular radial barrier satisfies

```text
M_sym(n,p) <= epsilon^(-d) C_n/(1-epsilon^3 P).        (8)
```

This is a global bound on the regular maximum, not a comparison at the same
radius.

## 4. Exact separation in both moved degrees

Both sides of (4) and (8) scale as `epsilon^(-d)`.  The correction factor on
the lower bound worsens monotonically with `epsilon`, while the correction
factor on the upper bound also worsens monotonically with `epsilon`.
Consequently it suffices to compare them at `epsilon=1/600`.

Cubing the squared inequalities removes every cube root in (7).  The exact
rational replay proves

```text
[A_5/D(1/600)]^6 > [C_5/(1-P/600^3)]^6,
[A_6/D(1/600)]^6 > [C_6/(1-P/600^3)]^6.                (9)
```

The ratios of the left sides to the right sides are respectively larger
than `1.3006` and `1.0858`; the displayed decimals are only orientation,
while (9) is checked as a positive integer comparison.  Combining
(4), (8), and (9) yields

```text
max_(q in [epsilon b_2,1])
  q^(-n)|B_epsilon(q u_2)|
  > M_sym(n,epsilon^3P),       n=5,6.                  (10)
```

The left side is the barrier of the actual radial curve to the closest
excluded root.  Thus (10) is attachment-compatible and defeats the
closest-root choice after full radial optimization, not merely at a
pointwise comparison radius.

## Frontier effect and exact boundary

The failure occurs in the low-capacity asymptotic itself, so a proof cannot
splice the near-saturation full-critical-numerator theorem to a rule that
chooses the closest excluded root below the saturation collar.  The surviving
possibilities are genuinely adaptive:

1. minimize the optimized barriers over all three actual roots;
2. use a root-selection statistic which retains angular data and is allowed
   to reject the closest root;
3. control the true curved mountain-pass attachment instead of a prescribed
   radial curve.

This theorem does not show that every root ray is too expensive, does not
bound the least exterior critical value from below, and does not produce an
abstract exterior model from a polynomial component.  It preserves the live
optimized-ray and mountain-pass conjectures.

## Replay

```sh
./repo-python formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1041/scripts/check_erdos1041_three_exterior_closest_ray_low_capacity_nogo.py
```

The checker uses `fractions.Fraction` only.  It verifies the rational unit
vectors, strict speed bound, exact distance product, domain inclusion, and
both sixth-power separations.

## Research receipt

```text
tao_pipeline_receipt:
  input_stage: generation
  output_stage: verification
  artifact: ThreeExteriorClosestRayLowCapacityNoGo.md plus exact Fraction checker
  human_understanding_delta: low capacity does not rescue the closest-root selector; the selector must retain angular information and compare roots
  verification_state: ordinary exact proof with exact rational replay of every numerical separation
  publication_or_review_state: source-level research result, not independently reviewed
  canonicalization_state: one no-go family; endpoint inequalities are subordinate checks
  unresolved_downstream_bottleneck: optimize over all three actual rays or control the curved mountain pass
  next_stage_owner: active Erdős 1041 exterior-selector proof lane

paper_assimilation:
  paper: erdos-1041-lemniscate-newton-flow
  section: exterior finite-Blaschke selector obstruction
  canonical_mechanism_family: low_capacity_closest_root_selector_nogo
  relation: exact obstruction to one stronger selector, not a solution of the parent
  understanding_delta: near-saturation rigidity cannot be patched below its collar by always taking the closest excluded root
  evidence_boundary: abstract admissible exterior model; no polynomial realization or unrestricted theorem
  hard_step: compare one actual optimized ray from below with the entire algebraic regular maximum from above uniformly in epsilon
  meaningful_failed_route: closest-root radial attachment in moved degrees two and three
  open_remainder: adaptive min-ray selector, angular statistic, or curved mountain-pass envelope
```
