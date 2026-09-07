# Erdős #1041: three exact obstructions from the 2026-09-06 revision return

Status: ordinary exact refutations with Lean-checked rational cores.
2026-09-06. None of these is a counterexample to Erdős #1041.

Replay:

```sh
./repo-python formal_math/erdos257_period_noncollapse/ErdosProblems/Erdos1041/scripts/check_erdos1041_r2_revision_exact_cores.py
cd formal_math/erdos257_period_noncollapse && \
  ../../repo-python scripts/lean_fast_build.py --jobs 2 \
  ErdosProblems.Erdos1041.RevisionR2ExactCores
```

## Collision against occupied theorems

- The all-degree monic trinomial theorem is already
  `abel_control_polygon_and_all_degree_trinomial_conclusion` /
  `trinomial_erdos1041_conclusion`. It is not re-registered. It is the
  cleanest proved all-degree connector that actually hits length `< 2` inside
  `{|f|<1}` for a complete family, so it belongs on page one of the note.
- Type B's Bergman identity
  `(∫_{-1}^1 |F'| dt)^2 ≤ (4/π) artanh(R^{-2}) E` is Lemma A of
  `BergmanSegmentLengthBound.md` with `q = 1/R`. It is not re-registered.
  The proposed all-degree cutoff `S = 3/2` for the old coefficientwise
  first-merge bound is strictly weaker than the already landed disk-family
  theorem (`S = 4/3` in every degree `n ≥ 3`, limiting cutoff `coth 1`).
- The one-root gamma perimeter bound was already floating-refuted on
  `z^n - z` in `DegenerateHubBlaschkeReduction.md`. The degree-eight witness
  below is the first exact algebraic comparison that does not use a numerical
  perimeter tracer.

## 1. SEP-OR is false

Let

```text
f(z) = z^3 + (3/100) z - 3/4.
```

On `|z| = 1` one has `| (3/100)z - 3/4 | ≤ 39/50 < 1 = |z^3|`, so Rouché
places all three zeros in the open unit disc. The critical points are the
simple zeros of `3z^2 + 3/100`, namely `c_± = ± i/10`, with values

```text
v_± = -3/4 ± i/500.
```

Thus `μ² = 9/16 + 1/250000 > (13/25)²` and `μ > 3/4`. The two values have
equal negative real parts and distinct nonzero imaginary parts, so they lie
on distinct positive rays. Direct substitution gives

```text
|1 - v_-/v_+| = 1/(250 μ) < 2/375 < 2.
```

Neither critical value is separated by two. The same strict margins persist
under small coefficient perturbations. The example is itself a trinomial, so
the radial theorem already joins its roots; the obstruction is to any covering
programme that would settle the residual `μ > 13/25` by “a critical value is
separated by two, or else first-merge arity, or else a capacity cutoff”.
Arity and capacity corollaries in the corpus assume `μ ≤ 1/2` and cannot fill
that residual.

## 2. The one-root gamma perimeter bound is false

Let `p(z) = z^8 - (3/2) z` and `K = {|p| ≤ 1}`. On `|z| = 4/5`,

```text
|p(z)| ≥ 6/5 - (4/5)^8 > 1,
```

and for every `|w| ≤ 1` Rouché on that circle compares `p - w` with `-3z/2`.
The connected component `C` of `K` containing zero therefore contains exactly
one zero. For `|z| ≤ 5/8`,

```text
|p(z)| ≤ 15/16 + (5/8)^8 < 1,
```

so a neighbourhood of the closed disc of radius `5/8` lies in the interior of
`C`. A positively oriented parametrisation of `∂C` has winding one about zero
and modulus strictly larger than `5/8`, hence

```text
H^1(∂C) > (5/8) · 2π = 5π/4.
```

The proposed constant `β = Γ(1/4)² / (2√π)` satisfies `β ≤ (π/2)(1 + √2)` by
the secant bound on `(1+x)^{-1/2}` over `[0,1]`, and `√2 < 3/2` gives
`(π/2)(1 + √2) < 5π/4`. No floating evaluation of a gamma value is used.

The binomial family `z^N - a z` with `a ↓ 1` shows that any degree-uniform
constant of this form must be at least `2π`. That does not prove `2π` is an
upper bound. At a quadratic first merger, a single petal is a component of
the open precritical sublevel, not a one-root component of the closed
critical sublevel, so the advertised Bernoulli equality case does not sit in
the stated class.

## 3. First-merge arity does not force a capacity gap

Let `g(z) = z^3 - (3/400) z - 3/32`. The critical points are `±1/20`, with

```text
g(-1/20) = -187/2000,     g(1/20) = -47/500,
```

so `μ = 187/2000 < 1/2` is a unique first-critical modulus. The first critical
point is simple and `g` is squarefree. For small positive levels there are
three one-root components; at the first simple saddle exactly two merge, so
the component of `K_μ` containing the first saddle has `k_0 = 2` roots. At
`T = 2μ = 187/1000` both critical values lie strictly inside the value disc.
Riemann–Hurwitz then gives a single component of `{|g| < T}`: a regular
sublevel with `b` components contains `n - b` critical points, here `2 = n-1`,
hence `b = 1`. For monic degree `n`,

```text
cap(K_T) = T^{1/n},
```

so the ancestor component `C` of `{|g| < 2μ}` has normalised capacity
`κ = 1`. All roots lie in the open unit disc by Rouché:
`3/400 + 3/32 = 81/800 < 1`. Thus `k_0 = 2` and `κ = 1` can coexist under
the corollaries' root and `μ` hypotheses. No estimate `κ ≤ τ_2 < 1` follows
from low first-merge arity alone: arity is measured at level `μ` and capacity
at level `2μ`, and a second merger occurs between those levels.

The arity and capacity corollaries remain valid as sufficient implications
under `μ ≤ 1/2`. They are not a covering of the residual `μ > 13/25`.
