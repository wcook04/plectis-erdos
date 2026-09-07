# ExternalVerification257GeneralRepairCriterion

## Statement

Let `mersenneWeight n = 1/(2^n - 1)`, let `greedyMersenneRemainder x` be the residual of the
greedy rule that subtracts `mersenneWeight (n+1)` whenever it fits, let
`greedyMersenneSupport x` be the set of positive exponents the rule selects, and let
`supportCoeff A n` count the divisors of `n` that lie in `A`. The greedy defect at scale `N`
is

    greedyBinaryDefect x N = ⌊2^N * x⌋₊ − binaryCoeffPrefixNumerator (supportCoeff (greedyMersenneSupport x)) N,

the dyadic numerator of the target minus the dyadic numerator already paid by the selected
exponents. Write `mersenneAchievementSet` for the set of reals of the form
`∑' k, 1_A (k+1) · mersenneWeight (k+1)` with `0 ∉ A`.

For every real `x ≥ 0`:

1. `x ∈ mersenneAchievementSet` if and only if for every `K` there is `N ≥ K` with
   `greedyBinaryDefect x (N+1) ≤ greedyBinaryDefect x N`;
2. `x ∈ mersenneAchievementSet` if and only if for every `K` there is such an `N` in the
   window `[K, K + 2·⌊√K⌋ + 12)`.

Both directions of both equivalences are proved.

## Mechanism

The greedy prefix numerator never exceeds `⌊2^N x⌋₊`, so the defect is a well-defined
sequence of natural numbers. A scale at which the defect does not increase is exactly a scale
at which the greedy rule recovers ground it had lost, which is what membership requires
cofinally. The window bound comes from the divisor bound `τ(n) ≤ 2√n`: the defect is
controlled by `2√N + 4`, so a run of strict increases longer than the window is impossible for
a member. The second form is what makes a finite search at each scale meaningful, because it
replaces an unbounded cofinal search by one of width `O(√K)`.

## Boundary

The criterion is a reformulation of membership, and it decides no particular target. In
particular it does not decide whether one half lies in the achievement set, which is the
concrete question the surrounding programme studies. It supplies no infinite-support
irrationality argument and it is not a step toward one. **Erdős Problem #257 is open, and
nothing in this package bears on it.**

The window constant 12 is the constant carried by the source proof's divisor bound and is not
claimed to be optimal.

## Files

| File | Role |
|---|---|
| `Challenge.lean` | Mathlib-only re-declaration of the definition chain and the two statements, with `sorry` bodies. |
| `Solution.lean` | The same two statements, token-identical, proved by transporting the source theorems through one identification equation per definition. |
| `comparator.json` | The two compared theorem names and the three permitted axioms. |
| `formalization.yaml` | Metadata, claim boundary and provenance. |
| `AxiomAudit.lean` | `#print axioms` over both compared theorems. |

## Provenance and checking

The source theorems are `ErdosProblems.Erdos257.mem_iff_greedyBinaryDefect_cofinal_repairs`
(`ErdosProblems/Erdos257/GreedyRepairCriterion.lean`, line 175) and
`ErdosProblems.Erdos257.mem_iff_greedyBinaryDefect_sqrt_windows` (line 192).

With Lean `v4.29.1` and Mathlib `5e932f97dd25535344f80f9dd8da3aab83df0fe6`,
`Solution.lean` and `Challenge.lean` each elaborate at `rc=0` under focused single-file
checking, `Challenge.lean` reporting exactly the two intended `sorry` warnings, and
`#print axioms` over both compared theorems in `Solution.lean` returns exactly `propext`,
`Classical.choice` and `Quot.sound`.

The package is not yet registered in `lakefile.toml`, so no `lake build` of it has been run,
and no Comparator or NanoDa replay has been recorded. Nothing here is a Palomar verdict.
