# Erdős #257: the conditional four-ninths tetraprime frontier

This package exposes the strongest checked interface of a concrete
counterexample programme for Erdős #257.  It is not merely a reformulation of
the parent problem.  The Lean development proves an exact finite kernel,
compresses every repaired large-prime row to a defect ceiling, and reduces the
remaining all-depth work to two explicit arithmetic statements.  If those
statements hold, the greedy support at `4/9` is infinite, its Mersenne
subseries has exact rational value `4/9`, and the universal irrationality
assertion is false.

The two open statements are:

1. every prime `p > 7` repairs at the row `420p`;
2. every composite cofactor has five units of tetraprime-column margin.

These are genuine hypotheses, not results hidden behind the package.  The
large-prime boundary is the moving prime-column obstruction.  The composite
margin feeds an exact proper-divisor descent and strong induction.  The
checked finite kernel proves that the row-420 union load is `12`, the defect at
419 is `7`, and the prime cofactors `2, 3, 5, 7` repair.  A repaired prime row
above seven must have defect at most `35`, because the moving proper-divisor
column has width at most `23` and the fixed base load is `12`.

Computation finding no repair failure through fifty million is useful attack
evidence, but it is not a theorem and is not part of the Comparator claim.

## Exact correspondence

The declarations are presented in mathematical reading order: the strongest
conditional endpoint first, followed by the proved finite kernel and the
large-prime compression mechanism.

| Comparator declaration | Exact paper route | Checked source route | Honest boundary |
|---|---|---|---|
| `fourNinthsTetraprime_completeCounterexample` | `res:four-ninths-tetraprime`; mechanism `sec:four-ninths-tetraprime`; boundary `bdry:four-ninths-tetraprime` | `FourNinthsPrimorialRepair.lean:1417`, `:1424`, `:1450`; `FourNinthsCofinalRepairConsumer.lean:394`, `:473` | assumes the large-prime boundary and five-unit composite margin |
| `fourNinthsTetraprime_baseKernel` | `res:four-ninths-tetraprime` | `FourNinthsPrimorialRepair.lean:497`, `:535`, `:583` | proves the base row and primes at most seven only |
| `fourNinthsTetraprimePrimeRepair_defect_le_thirty_five` | `res:four-ninths-tetraprime` | `FourNinthsPrimorialRepair.lean:840` | assumes repair of the selected large-prime row |

The authoritative public paper base is pinned at
[c7f752d0aec77a29ef852ddc2e805ccc38f7a609](https://github.com/wcook04/plectis-lean-erdos249-257/blob/c7f752d0aec77a29ef852ddc2e805ccc38f7a609/paper/erdos-257-mersenne-support-subseries.tex).
That version does not yet contain this family.  The source-current revision is
staged in
[`ErdosProblems/papers/erdos-257-mersenne-support-subseries.patch`](../ErdosProblems/papers/erdos-257-mersenne-support-subseries.patch).
The stable labels above become live paper routes only after operator-authorized
promotion of that patch.

## Editorial signal and ordering

The provisional Plectis Signal is `95/100`:

- mathematical advancement: `42/45`;
- parent-problem proximity: `20/20`;
- theorem strength: `14/15`;
- mechanism depth: `10/10`;
- consequence reach: `9/10`.

This is a portfolio-relative editorial reading priority, not proof authority,
novelty, Comparator replay, Palomar acceptance, mechanical readiness, or
submission authorization.  It is high because a sharp partial counterexample
programme with a proved finite kernel and a two-obligation terminal reduction
substantially advances the attack.  No rigid theorem-type ladder is being
used: a consequential partial proof or attack-changing weaker statement may
properly outrank an exact equivalence.

## Comparator boundary

`Challenge.lean` imports only Mathlib and contains the three trusted
specification declarations. `Solution.lean` transports and composes the exact
source theorems. `NegativeSolution.lean` deliberately changes all three
declaration types, so a supported Comparator run must reject it with the named
mismatches. `AxiomAudit.lean` prints the selected declarations' axiom closure.
NanoDa is enabled and the permitted budget is exactly `propext`, `Quot.sound`,
and `Classical.choice`.

Focused local validation is run from
`formal_math/erdos257_period_noncollapse`:

    ../../repo-python scripts/lean_fast_build.py --jobs 2 \
      ErdosProblems.Erdos257.FourNinthsPrimorialRepair \
      ExternalVerification257FourNinthsTetraprime.Challenge \
      ExternalVerification257FourNinthsTetraprime.Solution \
      ExternalVerification257FourNinthsTetraprime.NegativeSolution \
      ExternalVerification257FourNinthsTetraprime.AxiomAudit

The existence of this route is not a replay verdict. Terminal positive
acceptance and deliberate-negative rejection on a supported runner remain
separate gates. The paper revision, Comparator package, and Palomar portfolio
record must all carry the same statements, labels, boundary, score, and order
before any external submission is treated as ready.
