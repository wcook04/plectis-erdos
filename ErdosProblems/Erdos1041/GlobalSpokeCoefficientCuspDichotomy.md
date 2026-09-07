# Erdős 1041: a global coefficient collar and the exact cusp residual

## Status

This note proves an all-degree, all-root straight-spoke theorem for a weighted
coefficient collar.  It then composes that global producer with the one-row
critical-spoke selector and the source-current near-Fekete transverse theorem.
The result is an exact three-way reduction: after the two straight producers
fail, a near-Fekete obstruction must be angular-dominated; if its linear mode
is quantitatively present, the curved cusp theorem closes it.  The only
near-Fekete remainder is therefore a multi-mode higher-tangent angular cusp.

This is an ordinary analytic theorem with an exact symbolic checker.  It does
not prove that every polynomial enters one of the three closed cones, and it
does not close the higher-tangent remainder.

## 1. A scalar endpoint inequality

For integers `1<=k<n` and `0<=t<=1`,

```text
n(t^k-t^n) <= (n-k)(1-t^n).                                (1)
```

Indeed

```text
phi(t)=n t^k-k t^n,
phi'(t)=nk t^(k-1)(1-t^(n-k))>=0,
phi(t)<=phi(1)=n-k,                                        (2)
```

which is (1).  The constant `(n-k)/n` is sharp as `t` tends to one.

## 2. Global weighted-coefficient collar

Write a monic polynomial as

```text
P(z)=z^n+sum_(k=1)^(n-1)b_k z^k+c                         (3)
```

and assume all of its roots lie in the open unit disk.  Vieta gives `|c|<1`.
For a root `a`, the root equation gives the endpoint-vanishing identity

```text
P(t a)=c(1-t^n)+sum_(k=1)^(n-1)b_k a^k(t^k-t^n).           (4)
```

Define the root-specific and global weighted defects

```text
W(a)=sum_(k=1)^(n-1)(n-k)|b_k||a|^k,
W   =sum_(k=1)^(n-1)(n-k)|b_k|.                            (5)
```

> **Theorem A (weighted-coefficient radial collar).**  Every root `a`
> satisfying
>
> ```text
> W(a)<=n(1-|c|)                                           (6)
> ```
>
> has its complete origin spoke in `{|P|<1}`.  In particular, if
>
> ```text
> W<=n(1-|c|),                                             (7)
> ```
>
> every root spoke is safe and Erdős 1041 holds.

### Proof

By (1), (4), and (6), for `0<t<1`,

```text
|P(t a)|
 <= |c|(1-t^n)+sum_k |b_k||a|^k(t^k-t^n)
 <= |c|(1-t^n)+W(a)(1-t^n)/n
 <= 1-t^n
 < 1.                                                       (8)
```

At `t=0`, `|P(0)|=|c|<1`; at `t=1`, `P(a)=0`.  This proves containment.
Any two distinct roots may now be joined through the origin.  Their total
length is `|a_i|+|a_j|<2`, proving the last assertion.  ∎

There is a strictly broader two-root selector which keeps the individual root
radii instead of replacing them by one.  If the roots, with multiplicity, are
`a_1,...,a_n`, then

```text
sum_i W(a_i)
 =sum_(k=1)^(n-1)(n-k)|b_k| sum_i |a_i|^k.                 (8a)
```

> **Corollary (root-energy selector).**  If
>
> ```text
> sum_k(n-k)|b_k| sum_i|a_i|^k
>       <=n(n-1)(1-|c|),                                  (8b)
> ```
>
> then at least two root occurrences have safe origin spokes, and Erdős 1041
> holds.

Indeed, if at most one occurrence had `W(a_i)<=n(1-|c|)`, the other `n-1`
terms would make the left side of (8a) strictly larger than the right side of
(8b).  This can be substantially stronger than (7) when two inner roots pay
for the coefficient defect.

The weight in (5) is not cosmetic.  It is the sharp endpoint cost of the mode
`z^k`; replacing it by an unweighted coefficient norm loses the factor by
which high modes are cheaper near the root endpoint.

## 3. Explicit near-Fekete radial cone

Apply Theorem A to

```text
P(z)=z^n-R^n+epsilon h(z),
h(z)=sum_(k=1)^(n-1)h_k z^k,       0<R<1.                  (9)
```

It proves the full problem whenever

```text
epsilon sum_(k=1)^(n-1)(n-k)|h_k| <= n(1-R^n).             (10)
```

This is an explicit finite collar uniform over every coefficient phase and
including all tangent strata `h'(0)=0`.  It complements, rather than replaces,
`NearFeketeTransverseClosure.md`: (10) pays perturbation by the inward radial
slack, whereas that theorem gains curved-branch length from a quantitatively
nonzero linear splitting mode even when radial slack is too small to pay the
straight spokes.

The exact sparse family

```text
z^n+epsilon z-R^n,             0<epsilon<1-R^n             (11)
```

lies in (10), since `(n-1)epsilon<n(1-R^n)`.  Thus the family on which the
phase/energy hybrid envelope is numerically largest is not merely handled
asymptotically: every origin spoke is safe by Theorem A (and, independently,
by `CyclicTrinomialFiberCase.md`).

## 4. Composition with the critical row and curved cusp

At the minimum-critical-value hub, form the second-nearest one-row hybrid
`J_2` of `CriticalSpokeHybridLowModeDichotomy.md`.  There are now three exact
producers:

1. **critical row:** `|P(c_*)|J_2<=1` gives two contained spokes whose total
   length is at most two;
2. **global coefficient collar:** (7) gives every origin spoke and strict
   total length below two;
3. **transverse near-Fekete cusp:** after writing (9) with a normalized
   perturbation, every fixed cone
   `|h_1|>=eta ||h||` is closed for sufficiently small `epsilon` by curved
   inverse branches.

Consequently, a sequence in the near-Fekete regime which evades the first two
producers and is not already closed by the third must satisfy both

```text
epsilon sum_k(n-k)|h_k| > n(1-R^n),                         (12)
|h_1|/||h|| -> 0.                                           (13)
```

Equation (12) says the sequence is **angular-dominated** rather than radially
paid.  Equation (13) says it approaches the higher-tangent face.  If only one
higher mode survives, the exact centred-trinomial theorem closes it at every
scale.  The genuine residual is therefore:

```text
angular-dominated + vanishing linear mode + at least two competing
higher modes.                                               (14)
```

This is a strict reduction of the former undifferentiated near-Fekete tangent
stratum.  It does not assert that failure of the critical row alone forces
near-Fekete proximity; the bulk still requires its own selector.

## 5. Adversarial calibration

The checker replays (1), (4), and (8) exactly and stress-tests the collar on
degrees `5` through `13`.  A separate deterministic angular perturbation sweep
used roots of modulus `1-10^-9`.  Failures of the *straight critical hybrid
certificate* occurred only at high Fekete ratios in that sweep: the smallest
observed ratios by degree lay between `0.9601` and `0.9923`.  The normalized
linear coefficient ratio could nevertheless be as small as `0.0021`, so no
uniform transverse constant `eta` may be inferred from hybrid failure.

Those values are float evidence only.  Their role is to identify (14), not to
prove a global implication from a sampled threshold.  The exact open boundary
remains a producer for the multi-mode higher-tangent angular cusp, together
with the non-near-Fekete bulk where neither straight certificate is forced.
