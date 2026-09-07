# All-degree sharp occupied cone for two critical spokes

## Status

This note extracts an all-degree closed cone from the critical-spoke energy
majorant of `CriticalSpokePhaseMomentHybrid.md`.  It is an ordinary exact
theorem with a symbolic checker.  It closes every critical row whose two
largest reciprocal weights occupy the stated fraction, but it does not select
such a row globally.

## 1. Energy row

Let

```text
P(z)=product_(k=1)^n(z-a_k),   n>=2,   P'(c)=0,   P(c)!=0,
d_k=|a_k-c|,
p_i=d_i^(-2)/sum_k d_k^(-2),
S_i=(1-p_i)/p_i.
```

On the straight spoke `c+t(a_i-c)`, `0<=t<=1`, the source-current AM--GM
row is

```text
|P(c+t(a_i-c))|/|P(c)|
 <= F_(n,S_i)(t)
 :=(1-t)[1+(2t+S_i t^2)/(n-1)]^((n-1)/2).        (1)
```

## 2. Sharp scalar cone

Put `alpha=2/(n-1)`.  The binomial series has positive coefficients and

```text
(1-t)^(-alpha)
 =1+2t/(n-1)+(n+1)t^2/(n-1)^2
   +sum_(k>=3) (alpha)_k t^k/k!.                 (2)
```

Therefore

```text
S <= (n+1)/(n-1)                                  (3)
```

implies

```text
1+(2t+S t^2)/(n-1) <= (1-t)^(-2/(n-1)),
F_(n,S)(t)<=1.                                    (4)
```

For `0<t<1`, (4) is strict even at equality in (3), because the cubic and all
higher coefficients omitted from (2) are positive.

The threshold is sharp for this energy row.  If `S>(n+1)/(n-1)`, the
quadratic coefficient of

```text
1+(2t+S t^2)/(n-1)-(1-t)^(-2/(n-1))
```

is positive; hence `F_(n,S)(t)>1` for every sufficiently small positive `t`.

In reciprocal-weight form, (3) is exactly

```text
p_i >= (n-1)/(2n).                                  (5)
```

## 3. Two-spoke theorem

Order the reciprocal weights `p_1>=p_2>=...`.  If

```text
p_2 >= (n-1)/(2n),                                  (6)
```

then (5) holds for both nearest roots.  Both straight critical spokes lie in
`{|P|<=|P(c)|}`.  If `|P(c)|<1`, their concatenation lies in the open unit
lemniscate.  The geometric-mean two-nearest budget `(F)` of
`BarycentricEnvelope.md` gives

```text
d_1+d_2 <= 2 |P(c)|^(1/n) <2.                       (7)
```

Thus (6) at any subunit critical point is a complete Erdős #1041 certificate.

For `n=5`, (3), (5) are `S_2<=3/2`, `p_2>=2/5`; this is the cone used by
`BernsteinNoGoCriticalConeRescue.md`.  The theorem also shows precisely why a
pure occupied-cone global selector cannot be repaired by changing constants:
the scalar threshold is already optimal for (1).  Rows beyond (6) require
the retained phase moments/full `J2` splice or the curved near-Fekete
connector.

## 4. Replay and boundary

Run

```text
./repo-python formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1041/scripts/check_erdos1041_all_degree_critical_occupied_cone.py
```

The checker verifies the coefficient identities, the positive binomial tail,
the weight equivalence, and the sharp quadratic sign in exact arithmetic for
degrees `2..100`, with a symbolic rational-parameter identity as the
degree-free kernel.

Proved: the all-degree sharp energy cone and its target consumer.  Not proved:
existence of a critical point satisfying (6), the full Bernstein-or-`J2`
allocation, or unrestricted Erdős #1041.
