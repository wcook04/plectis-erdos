# Erdős #1049: the 7/2 numerical-height Comparator object

This directory isolates one small, source-backed statement for independent
formal review:

\[
  \log 2 / \log 7 < \tfrac12 - 1/\pi^2.
\]

The declaration is a numerical entrance condition for the rational base
`7/2` in Bundschuh--Väänänen's published height theorem.  It is not a Lean
formalization of that analytic theorem and it does not claim irrationality at
`7/2`, a result for the open base `3/2`, or a solution of Erdős Problem 1049.

## Submission boundary

This directory documents a mechanical Comparator fixture. It is not a
Comparator verdict or a standalone Palomar research claim. A submission that
retains this nested project must select
`formal_math/erdos257_period_noncollapse` and explicitly provide its
repository-relative `comparator.json`, while the complete checked-out
repository still has to satisfy Palomar's 500 MiB limit and keep its single
conventional licence file at repository root. The current preparation does not
establish the separate research-interest decision or either terminal replay;
those conditions must be satisfied on one immutable public commit before any
Palomar eligibility is claimed.

The Challenge import boundary is part of that eligibility check. Palomar
requires the Challenge transitive import closure to stay within Lean core and
the named allowlisted libraries. This fixture's Challenge directly imports
only `Mathlib.Analysis.Real.Pi.Bounds` and
`Mathlib.Analysis.SpecialFunctions.Log.Basic`, both within the allowlist
`Init`, `Std`, `Batteries`, `Mathlib`, `TauCeti`, and `CSLib`. The checked-in
replay actuator fails closed when a direct Challenge import leaves that
allowlist, then the supported Comparator run remains responsible for the
terminal transitive-closure verdict. A future Challenge edit must preserve
this boundary and rerun the supported pair; the local preflight is not itself
a Palomar verdict.

## What the local proof checks

`ErdosProblems/Erdos1049/RationalBaseLambert.lean` supplies the elementary
certificate in four transparent steps:

1. `2 ^ 18 < 7 ^ 7` is checked by exact integer arithmetic.
2. Logarithmic monotonicity converts that certificate to
   `log 2 / log 7 < 7 / 18`.
3. `pi > 3` gives `7 / 18 < 1 / 2 - 1 / pi ^ 2`.
4. The two strict inequalities prove the local height predicate.

The compared declaration in `Challenge.lean` is deliberately only the final
inequality.  The positive entry resolves to
`ExternalVerification1049.Solution`, whose source file
`ExternalVerification1049/Solution.lean` proves that same name and type by
transporting the local certificate.  The analytic implication and its
inherited source hypotheses remain external evidence.

## Comparator surfaces

The canonical positive one-entry configuration is the project-root
`comparator.json` at `formal_math/erdos257_period_noncollapse/comparator.json`.
The separate `formal_math/erdos257_period_noncollapse/ExternalVerification1049/comparator-negative-mismatch.json` binds
`NegativeSolution.lean`, whose same-named declaration changes the strict
inequality to a weak inequality and adds a hypothesis.  The positive
configuration should be accepted and that deliberate mismatch rejected; no
such run is inferred from these files alone.  Both configurations request the
additional NanoDa kernel with `enable_nanoda: true`, so a supported replay
exercises the same two-kernel environment for the positive and negative cases.
Palomar's current policy treats this optional field as non-authoritative and
runs its own NanoDa-enabled verification; these local config files are not a
Palomar replay receipt.

From the selected project root `formal_math/erdos257_period_noncollapse`, run
the checked-in verifier on a supported Linux runner:

```sh
./scripts/verify-comparator.sh
```

It bootstraps the pinned Comparator, Landrun, NanoDa, and the
v4.29.1-matched `lean4export`, then runs the canonical positive configuration
and the deliberate negative.  The positive run must terminate successfully;
the negative run must terminate unsuccessfully with a declaration name/type
mismatch naming
`Erdos249257.ExternalVerification1049.comparator_sevenHalves_numericalHeight`.
This is the supported replay route, not a replay receipt.  The local `lake
env lean` checks below compile the three fixtures and run the checked-in axiom
audit, but do not establish Comparator acceptance or Palomar review.  Refresh
the [Palomar
submission rules](https://palomar-registry.org/how-to-submit) and the
[pinned Palomar policy](https://github.com/PalomarRegistry/PalomarPolicy/blob/d5a647db3757303b1d928cfae4d3d232eed3e79e/CONTRIBUTING.md)
before any operator-authorized submission.

The checked-in replay actuator runs both fixtures with the same systemd
boundary and emits one JSON result.  From the project root, run:

```sh
python3 ErdosProblems/Erdos1049/scripts/run_comparator_replay.py
```

It exits `0` only when the positive fixture is accepted and the deliberate
negative fixture is rejected with the expected declaration-mismatch diagnostic.
It exits `75` when the required Linux `systemd-run`/Comparator environment is
unavailable, rather than turning an unavailable host into a verdict.

The CI job prefixes the preserved replay log with the checked-out commit, the
project toolchain, and SHA-256 identities for the positive and deliberate-
negative configs plus the three Lean inputs. Its uploaded artifact name carries
that commit SHA and the unique workflow run ID. Those fields identify the
inputs; the verifier's final positive/negative result lines remain the actual
replay evidence.

For a local Lean check from the project root:

```sh
lake env lean ExternalVerification1049/Challenge.lean
lake env lean ExternalVerification1049/Solution.lean
lake env lean ExternalVerification1049/NegativeSolution.lean
lake env lean ExternalVerification1049/AxiomAudit.lean
```

The fourth command runs the checked-in `#print axioms` audit for the positive
Comparator declaration; its expected output is the standard Lean core set
`propext`, `Quot.sound`, and `Classical.choice`.

The root `formalization.yaml` records provenance, scope, automation, review
status, and the Apache-2.0 licence.  The primary source is Bundschuh and
Väänänen, *Arithmetical investigations of a certain infinite product*,
Compositio Mathematica 91 (1994), Theorem 2 on printed p. 177 (PDF p. 4):
<https://numdam.org/item/CM_1994__91_2_175_0.pdf>.
