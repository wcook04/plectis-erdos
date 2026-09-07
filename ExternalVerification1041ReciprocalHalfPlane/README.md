# Erdős #1041: reciprocal Newton-vector half-plane support

This directory isolates the source-backed sign lemma used in the reciprocal
description of the #1041 Newton vector:

```text
When all rotated root displacements lie in a closed right half-plane, the
outward component of the reciprocal Newton vector is nonpositive.
```

`Challenge.lean` states that literal result with only Mathlib imports.
`Solution.lean` proves the same name and type by transporting
`ErdosProblems.Erdos1041.newtonReciprocalVector_supportingHalfPlane` from the
source module.  The negative configuration adds an irrelevant `True`
hypothesis, producing a deliberate declaration-type mismatch for replay.

This is a local supporting-half-plane inequality.  It does not establish a
global path-length bound, prove the required geometric cover, or solve
unrestricted Erdős #1041.  It is also not a claim of Comparator acceptance,
Palomar qualification, novelty, or peer review.

On a supported Comparator host, run both configurations from
`formal_math/erdos257_period_noncollapse`:

```sh
systemd-run --property=RestrictAddressFamilies=~AF_UNIX --user --pty \
  -E PATH="$PATH" --working-directory "$PWD" -- \
  bash -c 'lake env comparator ExternalVerification1041ReciprocalHalfPlane/comparator.json'

systemd-run --property=RestrictAddressFamilies=~AF_UNIX --user --pty \
  -E PATH="$PATH" --working-directory "$PWD" -- \
  bash -c 'lake env comparator ExternalVerification1041ReciprocalHalfPlane/comparator-negative-mismatch.json'
```

The positive run should succeed.  The negative run should reject the
solution theorem because its declaration has the extra `hweak : True`
argument.  These commands are replay recipes only; a local Lean compile does
not imply Comparator acceptance or Palomar review, and this directory
performs no outbound action.
