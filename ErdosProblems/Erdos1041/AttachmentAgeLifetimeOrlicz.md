# Erdős 1041: attachment age is the exact Orlicz coordinate of lifetime

## Status

This note sharpens the interface between `EntranceEnergyRatioBridge` and the
full-forest lifetime budget.  A single merge-edge lifetime is an exact
universal nonlinear transform of its attachment-age increment.  In
particular, no positive linear conversion from age to lifetime is possible;
the correct currency is an Orlicz sum.  This is a proved reduction, not yet a
proof of unrestricted Erdős 1041.

## 1. The universal transform

Recall

```text
lambda_k(q)=log((1+q^(2/k))/(1-q^(2/k))),
I_k(r)=integral_r^1 dq/(q lambda_k(q)).
```

For one ancestor edge whose child has size `k`, put

```text
r=beta_child/beta_parent,
x=(1/k)log(1/r).
```

Thus `x` is exactly that edge's contribution to the root-labelled attachment
age.  Define the degree-free function

```text
Phi(x)=integral_0^x dt/log(coth t),   x>=0,
Phi(0)=0.
```

### Theorem A (exact lifetime-age transform)

For every integer `k>=1` and `0<r<=1`, with
`x=(1/k)log(1/r)`,

```text
I_k(r)=k Phi(x).                                      (AO1)
```

### Proof

Set `q=exp(-kt)`.  Then `dq/q=-k dt`, the endpoints `q=1,r`
become `t=0,x`, and

```text
q^(2/k)=exp(-2t),
(1+exp(-2t))/(1-exp(-2t))=coth t.
```

Substitution gives `(AO1)`.

The integrand `1/log(coth t)` is positive and strictly increasing on
`(0,infinity)`, because `coth t` and hence `log(coth t)` are strictly
decreasing.  Consequently `Phi` is increasing and strictly convex.

## 2. Sharp scalar consequences

### Theorem B (there is no uniform linear age charge)

For every fixed `k>=1` and every `c>0`, there exists `0<r<1` such that

```text
I_k(r) < c (1/k)log(1/r).                              (AO2)
```

Indeed, for `x>0`, monotonicity of the integrand gives

```text
0 <= Phi(x)/x <= 1/log(coth x) -> 0  as x->0+.
```

Then `(AO1)` gives `I_k(r)/x=k Phi(x)/x ->0` with
`r=exp(-kx)`.  Thus a packet asking for a universal estimate
`lifetime >= c * attachment_age` is asking for a false theorem.  Very rapid
mergers have age larger than lifetime by the logarithmic boundary factor.

### Theorem C (large individual age is expensive, nonlinearly)

For `x>0`, monotonicity on the upper half of the interval gives

```text
Phi(x) >= x/(2 log(coth(x/2))).                         (AO3)
```

Hence

```text
I_k(r) >= kx/(2 log(coth(x/2))).                        (AO4)
```

This is the correct one-edge statement: the conversion is weak near zero but
grows exponentially for large age.

## 3. Exact chain currency

Let a root pass through `m` ancestor edges.  On edge `j`, let the child size
be `k_j>=2`, the merge ratio be `r_j`, and

```text
x_j=(1/k_j)log(1/r_j),
A=sum_j x_j,
K=sum_j k_j.
```

Then Theorem A gives the exact root-path ledger

```text
L_path=sum_j I_(k_j)(r_j)=sum_j k_j Phi(x_j).           (AO5)
```

Convexity and weighted Jensen imply

```text
L_path >= K Phi((sum_j k_j x_j)/K)
       >= K Phi(2A/K).                                  (AO6)
```

The second inequality uses `k_j>=2` and monotonicity of `Phi`.  The coarser
cardinality-only form is

```text
L_path >= 2m Phi(A/m).                                  (AO7)
```

If the ancestor component has at most `n` roots, then `m<=n-2` and
`K<=2+3+...+(n-1)=n(n-1)/2-1`.  These give explicit degree-dependent lower
bounds, but they deliberately do not pretend to be degree-uniform.  Splitting
a fixed age among many extremely rapid edges is precisely the regime where a
scalar linear argument loses its force.

## 4. Root-summed age cancels every subtree-size denominator

Fix an internal component `v` with root set `S_v`, `|S_v|=k_v`.  Let `u`
range over the nontrivial proper descendant components of `v` whose parent
still lies below or equals `v`.  Write

```text
r_u=beta_u/beta_parent(u).
```

### Theorem D (root-summed age/product identity)

```text
sum_(i in S_v) A_i(v)
  = sum_(u below v) log(1/r_u)
  = log product_(u below v) (1/r_u).                    (AO8)
```

### Proof

The edge `u -> parent(u)` contributes

```text
x_u=(1/k_u)log(1/r_u)
```

to exactly the `k_u` descendant roots in `S_u`.  After summing over roots,
its coefficient is therefore `k_u*(1/k_u)=1`.  Summing over all internal
edges proves the first equality; the second is the logarithm product law.

### Corollary D1 (sharp two-young-root selector)

There are two distinct roots `i,j in S_v` such that

```text
max(A_i(v),A_j(v))
 <= [sum_(u below v) log(1/r_u)]/(k_v-1).               (AO9)
```

Indeed, order the nonnegative ages `a_1<=a_2<=...<=a_(k_v)`.  Since the last
`k_v-1` entries are at least `a_2`, `(k_v-1)a_2<=sum a_i`; choose the first
two roots.  The constant `1/(k_v-1)` is sharp for arbitrary nonnegative age
vectors, attained in the limit by `(0,c,...,c)`.

This is the first unconditional attachment-compatible pair selector in the
new coordinates.  It reduces the missing pair-age bound to an upper bound on
one component's internal merge-ratio product, a quantity already adjacent to
the merge-discriminant and transported-antichain lanes.

## 5. Consequence for the closing problem

Combining this note with `EntranceEnergyRatioBridge`, the exact data on a root
path are now

```text
q_i^2=beta_v^(2/k_v)Y_(i,v)^2 exp(-2A_i(v)),
L_i(v)=sum_(edges on i-to-v) k_e Phi(x_e),
A_i(v)=sum_(edges on i-to-v) x_e.                       (AO10)
```

Therefore the surviving allocation theorem cannot merely compare the two
scalar sums `A_i(v)` and `L_i(v)` linearly.  It must use at least one of:

1. the full Orlicz distribution of the edge ages `x_e`;
2. Theorem D's exact sharing of the same edges by all descendant root paths;
3. transported antichains, which price branching rather than one path;
4. Gram-good or metric weights that select two compatible young roots before
   the age is fragmented.

This is a strict improvement of the frontier: the former vague
"large age pays lifetime" premise has been replaced by the exact functional
and its sharp linear no-go.  The most promising global quantity is the
root-multiplicity-weighted Orlicz sum together with `(AO8)--(AO9)`, because
one internal edge contributes to every descendant root and can no longer be
hidden by inspecting paths one at a time.

## Verification

The checker verifies `(AO1)` at high precision over a deterministic grid,
checks monotonicity, convexity, `(AO3)`, both Jensen bounds, the near-zero
linear no-go, the exact root-summed identity and two-young-root selector on
every ordered binary tree through nine leaves, and actual-polynomial
merge-tree path ledgers in degrees three through eight.  The polynomial rows
are regression evidence; the proofs of `(AO1)` and `(AO8)` are the
substitution and double-counting arguments above.
