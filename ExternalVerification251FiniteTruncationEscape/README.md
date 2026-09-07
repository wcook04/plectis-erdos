# ExternalVerification251FiniteTruncationEscape

## Statement

Write `g n` for the `n`-th consecutive prime gap, zero-based, and

    T N = ∑' j, g (N + j + 1) / 2 ^ (j + 1)

for the complete real tail of the prime-gap dyadic series after index `N`. Fix
a majorant `M` with `g n ≤ M n` for every `n`. For a shift length `h`, an index
`N` and a block length `L`, the finite signed window is

    S = ∑ j < L, (g (N + h + j + 1) - g (N + j + 1)) / 2 ^ (j + 1)

and the majorant tail mass is

    R = ∑' j, (M (N + h + L + j + 1) + M (N + L + j + 1)) / 2 ^ (L + j + 1).

`cofinal_escape_of_finite_truncation` proves that if, for every fixed `h ≥ 1`
and every threshold `N₀`, some `N ≥ N₀` and some `L ≥ 1` have `R` summable and
`R < dist(S, ℤ)`, then every fixed positive shift `T (N + h) - T N` fails to be
integral cofinally.

`irrational_prime_series_of_finite_truncation` carries the same supply through
to irrationality of `∑' n, p n / 2 ^ (n + 1)`.

## Mechanism

The omitted part of the shift is identified exactly rather than estimated away:
after the length-`L` window it is the later complete shift scaled by `2 ^ (-L)`,
which the majorant bounds term by term. A real number whose distance to a
finite approximation is at most `E`, with `E` strictly less than the
approximation's own distance to the integers, is not an integer. Summability of
the majorant remainder is required only at the configurations the supply
actually names, which is weaker than convergence at every configuration.

## Boundary

The supply hypothesis is not proved here for the actual prime gaps, and it is
exactly the open input. The two theorems are a conditional criterion. They do
not settle Erdős Problem #251, which remains open.

## Provenance

Transported from `ErdosProblems/Erdos251/PaperTailBoundsR7.lean` in the private
`formal_math/erdos257_period_noncollapse` project. Toolchain
`leanprover/lean4:v4.29.1`, Mathlib `5e932f97dd25535344f80f9dd8da3aab83df0fe6`.
The source module elaborates rc 0 and its public theorems report only
`propext`, `Classical.choice` and `Quot.sound`.
