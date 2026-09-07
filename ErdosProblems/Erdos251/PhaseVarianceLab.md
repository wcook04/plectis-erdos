# Finite phase-variance criterion (ordinary research target)

Type B r3 file 05, Theorem 4.1 and Corollary 4.2. **Ordinary sufficient
criterion; the positive lower bound is unproved.** Collision-checked:
nothing in the live packet occupies a finite Fourier variance of truncated
phases `e(H_L(N))` on residue classes modulo a growing lcm schedule. Prefer
this as the research-target narrative alongside the signed count in
`MeanTailTruncationLab.md`. Do not enter the short note until the ordinary
statement is reviewed. The parent irrationality remains open.

## Statistic

Let `H_L(N) = ∑_{j=1}^L g_{N+j} 2^{-j}` and `u_L(N) = e(H_L(N))`. For
`t ≥ 1` and residue classes `I_a` in `[X, 2X)`,

```
V_t(X,L) = ∑_{a : I_a ≠ ∅} ∑_{N ∈ I_a} |u_L(N) - ū_a|^2.
```

This is exact complex algebra; each phase is a root of unity of order
dividing `2^L`. Evaluate from the integral block numerator modulo `2^L`,
not from a backwards floating-point tail.

## Rationality forces small variance

If `T_0 = a/(2^s d)` in lowest terms and `λ = ord_d(2)` (`λ = 1` for
`d = 1`), then whenever `X ≥ max(2,s)`, `1 ≤ L ≤ X`, and `λ ∣ t`,

```
V_t(X,L) ≤ C_V X log X · 2^{-L}.
```

The complete phase `e(T_N)` is constant on each `I_a` past the transient.
The sample mean minimises squared distances, and
`|e(z)-1|^2 ≤ 4π |z|` together with `T_N - H_L(N) = 2^{-L} T_{N+L}`
reduces the bound to the mean tail of `MeanTailTruncationLab.md`. The
constant is independent of the rational denominator and of `t`.

## One growing-modulus inequality

For large `X` put `t(X) = lcm(1,…,⌊log log X⌋)` and
`L(X) = ⌈(1+ε) log_2 log X⌉`. If `V_{t(X)}(X, L(X)) ≥ c X` on an unbounded
sequence of scales, then `Π` is irrational: under rationality the fixed
order eventually divides `t(X)`, and the upper bound is `o(X)`. Full
equidistribution is stronger than needed; positive variance suffices.

A certified lower bound requires trigonometric intervals or exact
cyclotomic arithmetic plus an ordered-real bound. Counting
positive-looking floating-point variance is not a certificate. No such
calculation is claimed here.

## Relation to bounded perturbation

Normalised statistics at scale `log X` are preserved by the registered
rationalising perturbation (`BoundedPerturbationCountermodel.lean`).
Unit-scale phases `e(T_N)` retain the information that division by
`log X` discards. Coarser randomness therefore does not yield parent
progress. The signed Land inequality remains an unproved sufficient
target (`SignedLandInequalityTarget.md`).

## Evidence class

Ordinary sufficient criterion. Lower bound unproved. Not Lean. Preferred
new analytic target because it replaces every fixed-shift obligation by an
explicit divisibility schedule, removes the exact `±2` gap condition, and
controls the omitted infinite tail.
