# Erdős #1041: a truncated path selected by the two smallest root moduli

Status: analytic all-degree case theorem proved on 2026-08-25 and current through
2026-08-27 replay. The
load-bearing factor and length inequalities are formalized in
`TwoSmallestRootTruncation.lean`. This is a genuine sufficient case of Erdős
#1041, not the unrestricted solution.

## The theorem

Let

```text
f(z) = product_(k=1)^n (z-z_k),       n >= 2,
```

be monic, with every root in the open unit disk. Order two roots `a,b` so that

```text
r=|a| <= q=|b| <= |z_k|       for every remaining root z_k.
```

Write the remaining root moduli as `s_3,...,s_n`. The strongest elementary
form is

```text
((r+q)^2/4) product_(k=3)^n (q+s_k) < 1.                 (TS-exact)
```

If this holds, the displayed path works. In particular, since every `s_k<1`,
the coefficient-free condition

```text
((r+q)^2/4) (1+q)^(n-2) <= 1,                              (TS)
```

then `a` and `b` are joined inside `{|f|<1}` by a polygonal path of length
strictly below two.

For `q>0`, write `u=a/r` when `r>0` and `v=b/q`. The path is

```text
a = r u  -->  r v  -->  q v = b.                           (P)
```

If `r=0`, use the single radius from `0=a` to `b`; the estimates below only
improve. Thus the theorem is an explicit instance of the Form A-cut reduction:
the smaller root itself is the common-radius endpoint on its ray.

The root-modulus-only corollary uses `(r+q)^2/4<=q^2`. The threshold `q_n`
defined by `q_n^2(1+q_n)^(n-2)=1` is unique in `(0,1]`. Numerically:

| `n` | 2 | 3 | 4 | 5 | 6 | 8 | 10 | 12 |
|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| `q_n` | 1 | .754878 | .618034 | **.528946** | .465571 | .380278 | .324718 | .285199 |

So, in particular, every quintic whose second-smallest root modulus is at most
`0.5289463545...` satisfies Erdős #1041, regardless of the smallest modulus.
The two-radius form (TS) is materially stronger: as `r->0`, it permits
`q<=0.8167478650...` in degree five.

## The selected-factor estimate

On the first segment put

```text
z = r((1-t)u+t v),       x=rt,       d=|u-v|<=2.
```

The two selected factors obey

```text
|z-a| = x d,
|z-b| <= r(1-t)+(q-rt) = q+r-2x.
```

Their product is at most `(r+q)^2/4`. The entire estimate is the square identity

```text
(r+q)^2 - 8x(q+r-2x) = (q+r-4x)^2 >= 0.                   (1)
```

On the radial segment write `z=xv`, `r<=x<=q`. Then

```text
|z-b| = q-x,       |z-a| <= x+r,
```

and again the selected product is at most `(r+q)^2/4`, now because

```text
(r+q)^2 - 4(q-x)(x+r) = (q-r-2x)^2 >= 0.                  (2)
```

Every point of (P) has modulus at most `q`. Hence the factor belonging to a
remaining root of modulus `s_k` is at most `q+s_k`. This proves (TS-exact).
Since `s_k<1`, every such factor is also strictly below `1+q`; multiplying (1)
or (2) by the `n-2` remaining factors gives

```text
|f(z)| < ((r+q)^2/4)(1+q)^(n-2) <= 1
```

on both pieces. This proves containment, including strictness.

## The metric estimate

The path length is

```text
r|u-v|+(q-r) <= 2r+q-r = r+q < 2,
```

because `r<=q<1`. Thus no separate ellipse or geodesic estimate is needed.

## Why this is useful and where it stops

This is not a close-pair theorem. The selected roots may point in opposite
directions and be almost `2q` apart; the proof pays for the long inner chord by
moving it to the smaller radius. It is also not a uniform-radius theorem: only
the second-smallest root must be small, while the other `n-2` roots may approach
the unit circle.

There is also a constant-term corollary. Since `q<=s_k`,
`q+s_k<=2s_k`. If `P=product_k |z_k|=|f(0)|` and `r>0`, (TS-exact) follows from

```text
2^(n-4) (r+q)^2 P/(rq) < 1.                               (CT)
```

Thus the mechanism can fire either because the second root is small or because
the constant term is small relative to the two selected radii.

The complement of both (TS-exact) and (TS) is real and contains the regular polygon equality
family, where every root modulus is one in the closed normalization. The next
unrestricted step therefore has to exploit angular balance, critical values,
or a moving hub; no root-modulus-only strengthening can remove that extremal
boundary.

## Verification and handoff

The checker `scripts/check_erdos1041_two_smallest_root_truncation.py` validates
the two exact scalar defects, the threshold table, and the full complex path
bound on randomized configurations through degree twelve. The Lean module
checks (1), (2), the strict multiplicative fan-in, and the length conclusion.
Its exact authority anchors are
[`twoSmallest_chord_twoFactor_bound#L21-L24`](TwoSmallestRootTruncation.lean#L21-L24),
[`twoSmallest_chord_selected_factor#L27-L39`](TwoSmallestRootTruncation.lean#L27-L39),
[`twoSmallest_factor_budget#L71-L87`](TwoSmallestRootTruncation.lean#L71-L87),
and [`twoSmallest_path_length_lt_two#L92-L100`](TwoSmallestRootTruncation.lean#L92-L100).

```sh
./repo-python formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1041/scripts/check_erdos1041_two_smallest_root_truncation.py
```

The 2026-08-27 replay reports `PASS` over 4,400 configurations, with worst
sampled value over budget `0.999999984440`; it also reproduces the displayed
thresholds through degree twelve. This validates the exact scalar/path-bound
consumer and does not promote the unrestricted theorem.

The Refinery should place this theorem beside `TruncatedSpokeReduction.md` as
its first coefficient-free analytic consumer. Preserve the unrestricted-open
boundary and route the complement `q^2(1+q)^(n-2)>1` back to the free-hub and
near-Fekete fronts.
