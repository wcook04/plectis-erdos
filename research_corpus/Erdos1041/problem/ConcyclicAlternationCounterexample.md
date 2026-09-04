# Erdős #1041: Conjecture U is false at five concyclic roots

Status, 2026-08-25: exact Gaussian-rational counterexample, exact-arithmetic
checker, and Lean-checked rational core. This refutes the concentric-alternation
law proposed in `ConcyclicFormACutCertificate.md`. It does **not** refute the
Form-A-cut inequality, the concyclic case of Erdős #1041, or Erdős #1041.

## Statement refuted

For distinct unit points `w_0,...,w_4`, put

```text
g(z) = product_j (z-w_j)
```

and let `G_k` be the closed counterclockwise gap from `w_k` to `w_(k+1)`.
Conjecture U asserted, for every `0<s<=1`,

```text
min_k max_{exp(i psi) in G_k} log |g(s exp(i psi))|
    <= log(1+s^5).
```

The following configuration violates the inequality at `s=3/20`:

```text
w_0 =   44/125   + (117/125)i
w_1 = -1809/2609 + (1880/2609)i
w_2 =   -4/5     - (3/5)i
w_3 =   24/145   - (143/145)i
w_4 = 1012/1013  - (45/1013)i.
```

Every `w_k` has squared modulus one. In the five gaps take

```text
x_0 = w_1,
x_1 = -9999/10001 + (200/10001)i,
x_2 = w_2,
x_3 = 91/109 - (60/109)i,
x_4 = w_4.
```

These also have squared modulus one. The cross-product tests

```text
cross(w_k,x_k) >= 0,   cross(x_k,w_(k+1)) >= 0
```

place `x_k` in the corresponding closed minor gap. Direct rational arithmetic
then gives

```text
|g((3/20)x_k)|^2 - (1+(3/20)^5)^2
  = 0.0019145951..., 0.0191027610..., 0.0078962976...,
    0.0070977608..., 0.0021883288...
```

respectively. Every gap therefore contains a point whose potential is strictly
larger than the regular-pentagon comparator. Hence the minimum of the five gap
maxima is also strictly larger, disproving Conjecture U.

## Why this is decisive and what survives

The margins are three to four orders above the earlier float-noise residuals.
The failure was missed because the earlier finite battery sampled only selected
basins; it is exactly the warning already attached to `negative_results` entry
19. The law fails far from the limiting `s -> 0` and `s -> 1` arguments: the
counterexample uses the ordinary rational radius `3/20`.

The Form-A objective remains viable. It asks for a gap chord with value at most
one at a radius compatible with two truncated spokes. Conjecture U instead
bounded every configuration by the regular value `1+s^5` at each prescribed
radius. This counterexample proves that this proposed uniform majorant cannot
be the missing bridge. Any surviving proof must select its radius jointly with
the spokes, or use a configuration-dependent comparator.

## Verification

`ConcyclicAlternationCounterexample.lean` checks the ten unit-circle identities,
the ten exact arc-orientation inequalities, and all five strict product
inequalities. The companion checker prints the exact rational margins and
requires all certificates to be positive.

```sh
./repo-python formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1041/scripts/check_erdos1041_concyclic_alternation_counterexample.py
./repo-python formal_math/erdos257_period_noncollapse/scripts/lean_fast_build.py --jobs 2 \
  ErdosProblems.Erdos1041.ConcyclicAlternationCounterexample
```
