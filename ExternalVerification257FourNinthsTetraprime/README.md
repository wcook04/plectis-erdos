# Erdős #257: the conditional tetraprime interface and its refuted producer

The large-prime repair hypothesis below is now refuted by a reviewed ordinary
proof. An exact selected prefix supplies 80 anchors; Dirichlet's theorem then
gives arbitrarily large prime cofactors with defect increase at least two at
`420p`. The proposed causal margin fails by at least three. See
[the full synthesis](../ErdosProblems/Erdos257/EightReturnSynthesis.md#3-consolidated-prime-cofactor-obstruction)
and its linked exact audit. The Lean conditional implication remains valid,
but this producer cannot supply a counterexample. Unrestricted cofinal repairs
and the universal problem remain open. This new obstruction is not a new
Comparator replay or Palomar acceptance.

This package retains a checked conditional interface of a concrete
counterexample programme for Erdős #257. The Lean development proves a finite kernel,
compresses every repaired large-prime row to a defect ceiling, and gives a
conditional implication from two explicit arithmetic statements. If those
statements hold, the greedy support at `4/9` is infinite, its Mersenne
subseries has exact rational value `4/9`, and the universal irrationality
assertion is false.

The two assumptions of the conditional theorem are:

1. every prime `p > 7` repairs at the row `420p` (now refuted);
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

The historical provisional Plectis Signal was `95/100`:

- mathematical advancement: `42/45`;
- parent-problem proximity: `20/20`;
- theorem strength: `14/15`;
- mechanism depth: `10/10`;
- consequence reach: `9/10`.

That pre-obstruction appraisal is superseded and must not rank the current
research frontier. It supplied no proof authority, novelty, Comparator replay,
Palomar acceptance, or submission authorization. Current allocation belongs
to the source-current research packet and its prime-cofactor obstruction.

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
