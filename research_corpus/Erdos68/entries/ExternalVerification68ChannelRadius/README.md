# Erdős #68: finite-channel radius obstruction

This package isolates the strongest quantitative endpoint of the checked
finite-channel method.  Write

\[
L_D=\operatorname{lcm}_{2\le d\le D}(d!-1).
\]

If `M > 0`, `L_{2t²}` divides `M`, and `M < (R+1)!-1`, then for
`t ≥ 2^32` the source theorem proves

\[
3t^3<2(R+1).
\]

The package also exposes the resulting eventual no-go and the coarser theorem
that `R(t)+1` cannot be little-o of `t³` under the corresponding all-large-`t`
hypotheses.  The hard input is a finite lower estimate for the channel lcm:
consecutive factorial gaps are combined while their pairwise gcd losses are
counted explicitly, and a Stirling bound converts that estimate into the cubic
radius obstruction.

## Boundary

These are conditional finite-channel theorems.  They do not construct `M` or
`R` from the factorial-gap series, prove that the required channels vanish, or
produce cofinally many non-unit carries.  They therefore do not prove the
irrationality of the series or solve Erdős Problem 68.

`Challenge.lean` imports only Mathlib and gives the literal definition of
`channelLCM`.  `Solution.lean` transports the three exact declarations from
`ErdosProblems.Erdos68.ChannelIntegralCongruence`.  The negative configuration
binds a same-named theorem with an extra `True` hypothesis and must be rejected
as a type mismatch.

## Validation

From `formal_math/erdos257_period_noncollapse`, run:

```sh
./scripts/lean_fast_build.py --jobs 2 \
  ExternalVerification68ChannelRadius/Challenge.lean \
  ExternalVerification68ChannelRadius/Solution.lean \
  ExternalVerification68ChannelRadius/NegativeSolution.lean \
  ExternalVerification68ChannelRadius/AxiomAudit.lean
```

The Comparator configuration permits exactly `propext`, `Quot.sound`, and
`Classical.choice`, and enables NanoDa.  A local package is not a Comparator or
Palomar verdict; replay, deliberate-negative rejection, public pinning, and
submission remain separate mechanical steps.
