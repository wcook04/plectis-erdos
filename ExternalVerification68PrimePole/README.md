# Erdős #68: finite prime-pole numerator formula

This directory isolates one exact finite identity for independent statement
and proof replay.  Let `q^e` be the positive maximal `q`-power dividing a
factorial gap `n! - 1` with `2 ≤ n ≤ M`.  When the finite reciprocal sum is
written over the literal prefix LCM, its numerator modulo `q` is the LCM
cofactor multiplied by the reciprocal sum of the cofactors at the maximal
`q`-adic hits.

## Mathematical boundary

`Challenge.lean` defines the four finite objects needed by the displayed
identity and imports only Mathlib.  `Solution.lean` transports
`ErdosProblems.Erdos68.factorialGapPrefixLCMNumerator_mod_prime` into the same
literal type.  The key step in the source proof is that every lower-valuation
summand vanishes modulo `q`, while the maximal layer factors through the
inverse cofactors in `ZMod q`.

The compared declaration concerns one finite prefix.  It does not assign a
`q`-adic valuation to the infinite real tail, prove that the finite residue is
nonzero, or prove irrationality of the Erdős #68 series.  The explicit
`q = 139` and `q = 2593` cancellation witnesses in the source development are
examples below this formula, not additional compared results.

## Comparator surfaces

`comparator.json` selects exactly the finite numerator theorem.
`comparator-negative-mismatch.json` binds `NegativeSolution.lean`, whose
same-named theorem has an extra `True` hypothesis.  A supported Comparator run
must accept the positive pair and reject that deliberate declaration-type
mismatch.  These files are replay inputs, not replay verdicts, Palomar
eligibility, peer review, or a claim about Erdős #68 itself.

From `formal_math/erdos257_period_noncollapse`, the source-local checks are:

```sh
lake env lean ExternalVerification68PrimePole/Challenge.lean
lake env lean ExternalVerification68PrimePole/Solution.lean
lake env lean ExternalVerification68PrimePole/NegativeSolution.lean
lake env lean ExternalVerification68PrimePole/AxiomAudit.lean
```

On a supported Comparator host, run the positive and deliberate-negative
configurations through the checked-in replay actuator:

```sh
./scripts/verify-comparator.sh
```

Exit `75` means that the required Linux systemd boundary is unavailable; it is
not a replay verdict.  No replay outcome is recorded merely because this route
exists.

## Palomar disposition

Do not submit this finite identity *by itself* as a Palomar entry.  That is a
claim-level judgment about one supporting lemma, not a verdict against Erdős
#68, its paper, or its principal exact result family.  The serious-note-grade
strict-successor carry/divisibility characterization now has its own dedicated
candidate configuration in `../ExternalVerification68StrictSuccessorCarry`.

Keep this formula as replayable subordinate evidence for that broader #68
result.  The main candidate still requires a public repository at a pinned
full commit, terminal positive and deliberate-negative Comparator results on a
supported host, and complete result-level metadata before submission.
