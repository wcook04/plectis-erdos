# Return 004: universal radial product and low-critical reduction

## Status

This note assimilates return 004 of
`erdos1041_20260826_return_stream_02`.  The return does **not** prove Erdős
#1041.  Its low-critical two-root conclusion is correct but is already
superseded by the stronger source-current theorem in
`GlobalCriticalTwoNearestBudget.md`: the two nearest roots to **every**
critical point have total distance at most `2`, without first selecting a low
critical value.

Two pieces of the return are mathematically correct:

1. the arbitrary-modulus radial product inequality, already landed as
   `exact_results::arbitrary_modulus_root_ray_product_contraction` in
   `TypeBReturnAssimilation20260826.md`;
2. a quantitative envelope controls a segment from a critical point to its
   nearest root.  Composing the return with the existing reciprocal-balance and
   every-critical metric theorems strengthens this to a complete two-spoke
   theorem in an explicit deep-low-critical regime.

Neither supplies the missing two-arm containment or the cyclic allocation
theorem.  The source-current parent residual remains safe straightening/COVER,
with combined charge as the other global target-deciding route.

## 1. Universal radial-product inequality

Let

```text
p(z) = product_j (z-a_j),       |a_j| <= 1.
```

For every `0 <= t <= 1`,

```text
product_i |p(t a_i)| <= 1.                              (RPI)
```

### Proof

Set

```text
F_t(a_1,...,a_n) = product_i p(t a_i)
                 = product_(i,j) (t a_i-a_j).
```

For fixed `t`, this is holomorphic in every root variable.  The maximum-modulus
principle on the root polydisc therefore reduces the estimate to
`|a_i|=1` for every `i`.  Write `a_i=exp(i theta_i)`.  Pairing the two ordered
off-diagonal factors gives

```text
|F_t| = (1-t)^n product_(i<j)
        (1+t^2-2t cos(theta_i-theta_j)).                 (1)
```

For `0<t<1`, let `P_t` be the Poisson kernel.  Direct differentiation and

```text
2(t-cos theta)/(1+t^2-2t cos theta) = (1-P_t(theta))/t
```

give

```text
d/dt log |F_t|
  = (n^2 - sum_(i,j) P_t(theta_i-theta_j))/(2t).
```

The Fourier expansion of the Poisson kernel yields

```text
sum_(i,j) P_t(theta_i-theta_j)
 = n^2 + 2 sum_(m>=1) t^m |sum_i exp(i m theta_i)|^2
 >= n^2.
```

Thus the boundary maximum is nonincreasing in `t`; at `t=0` it equals `1`.
Continuity handles the endpoints and proves (RPI).

This strictly extends the unit-circle identity in `TwoSegmentLevelIdentity.md`,
but the extension itself is already source-current in
`TypeBReturnAssimilation20260826.md`; return 004 independently reproduces it
and adds no stronger conclusion. Its quantifiers are still only

```text
for every t there exists i with |p(t a_i)| <= 1.
```

The exact Gaussian-rational ONE-SPOKE counterexample in
`VisibilityOverlapReduction.md` proves that one cannot exchange those
quantifiers.  Consequently (RPI) is an allocation currency, not a path theorem.

## 2. The low-critical statement is already dominated

For completeness, the return's discriminant step is valid.  For distinct roots
and critical points counted with multiplicity,

```text
product_i |p'(a_i)| = n^n product_j |p(c_j)|,
product_i |p'(a_i)| = product_(i<j) |a_i-a_j|^2,
product_(i<j) |a_i-a_j| <= n^(n/2).
```

Hence `product_j |p(c_j)|<=1`, so some critical value has modulus at most one.
If `d_1<=d_2<=...<=d_n` are its root distances, critical balance gives
`d_1>=d_2/(n-1)`.  Assuming `d_1+d_2>2` and splitting at
`d_2=2(n-1)/n` forces `product_k d_k>1`, a contradiction.

This proof is sound, but `GlobalCriticalTwoNearestBudget.md` and
`CriticalTwoRootProximity.lean` already prove `d_1+d_2<=2` for every critical
point.  No duplicate theorem is introduced.

## 3. Quantitative segment envelopes

Let `c` be a non-root critical point and `a_1` a nearest root.  Put

```text
x_k = (a_1-c)/(a_k-c).
```

Then `x_1=1`, `|x_k|<=1`, and `sum_k x_k=0`.  Along
`z(t)=c+t(a_1-c)`,

```text
p(z(t))/p(c) = product_k (1-t x_k).
```

Writing `y_k=1-Re x_k`, one has `y_1=0` and `sum_k y_k=n`.  Since

```text
|1-tx_k|^2 <= (1-t)^2 + 2t y_k,
```

AM--GM over `k>=2` gives

```text
|p(z(t))/p(c)|
 <= (1-t) (1+t^2+2t/(n-1))^((n-1)/2).                  (SEG)
```

For `n>=3` its maximum on `[0,1]` is

```text
C_n = 2/(n-1) * (2(n-2)/(n-1))^((n-1)/2).
```

Therefore `|p(c)|<=1/C_n` certifies the nearest spoke.

### A new two-spoke consequence

Let `a_2` be a second-nearest root and normalize instead by

```text
x_k=(a_2-c)/(a_k-c).
```

Critical balance and nearest ordering give

```text
|x_1|=|a_2-c|/|a_1-c| <= n-1,
|x_k|<=1 for k>=2,
x_2=1.
```

Hence along the second spoke,

```text
|p(c+t(a_2-c))/p(c)|
 <= (1-t)(1+(n-1)t)(1+t)^(n-2)
 <= n 2^(n-2).                                         (TWO2)
```

The nearest spoke has the smaller crude bound

```text
(1-t)(1+t)^(n-1) <= 2^(n-1) <= n 2^(n-2).              (TWO1)
```

Therefore:

> **Deep-low-critical two-spoke theorem.**  If `n>=2`, `p'(c)=0`, `p(c)!=0`,
> and
> `|p(c)| <= 1/(n 2^(n-2))`, then the straight segments from `c` to its two
> nearest roots both lie in `{|p|<=1}`.  By
> `GlobalCriticalTwoNearestBudget.md`, their total length is at most `2` when
> the roots lie in the closed unit disk.

This closes a genuine all-degree class.  If

```text
D = product_(i<j)|a_i-a_j|^2/n^n
```

is the normalized discriminant ratio, then
`min_c |p(c)| <= D^(1/(n-1))`.  Thus

```text
D <= (n 2^(n-2))^(-(n-1))                              (DISC)
```

implies the closed path theorem.  Scaling by the actual root circumradius
`R<1` gives length at most `2R<2` and level at most `R^n<1`, proving the
original strict statement for this discriminant class.

The threshold in (DISC) is deliberately crude and very small.  It turns the
return into a complete consumer on a nonempty all-degree regime, but it does
not approach the near-Fekete shell `D≈1`, where the unrestricted problem is
tight.

## 4. Attempted completion and exact surviving obstruction

Three possible completions were tested against the source-current corpus.

* **Connected component through a merely level-one critical point.**  A low critical point
  lies in a component containing at least two roots, but connectedness carries
  no intrinsic-length bound; winding polynomial lemniscates are the standing
  obstruction.
* **One safe radial spoke for all radii.**  This is exactly ONE-SPOKE and is
  refuted in degree five by the existing Gaussian-rational witness.
* **One critical point per unsafe radial/sector path.**  An unsafe radial bump
  only forces a zero of the radial derivative
  `Re(z p'(z)/p(z))`, not a zero of `p'`.  Several boundary superlevel strips
  can feed the same saddle.  Thus the proposed cyclic unsafe-path allocation
  lemma remains an unproved injectivity/multiplicity theorem rather than a
  consequence of ordinary mountain pass.

The smallest honest residual exposed by this return is:

> Convert the all-radius aggregate inequality (RPI), or the existing
> low-critical/metric budget, into a jointly allocated pair of safe arms or a
> COVER certificate, while allowing boundary strips to share critical points.

That residual is target-equivalent only after the missing allocation theorem is
proved; no solution claim is made here.

## 5. Disposition

| Returned item | Disposition |
|---|---|
| closed normalization and strict rescaling | superseded by `GenericSufficiencyClosure` |
| low-critical two-root theorem | superseded by the stronger every-critical theorem |
| universal radial-product inequality | superseded by the already-landed arbitrary-modulus theorem |
| centroid/variance core | superseded by the exact disc union in `BarycentricEnvelope` |
| nearest-segment envelope | strengthened and landed as a complete two-spoke theorem for `|p(c)|<=1/(n2^(n-2))`, hence an explicit discriminant class |
| Newton saddle-box warning | corroborates existing no-go corpus |
| cyclic unsafe-path allocation lemma | blocked: boundary-spoke injectivity is unproved |
