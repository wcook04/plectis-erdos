# Erdős #1041: staple-length identity

This directory isolates the affine length identity for an equal-radius staple:
the two root-modulus segments and the connecting segment combine into the root
sum minus the angular savings term.

`Challenge.lean` states the literal result with only Mathlib imports.
`Solution.lean` transports the same theorem from
`ErdosProblems.Erdos1041.ReciprocalNewtonExpansion`.  The negative fixture
adds an irrelevant `True` hypothesis, so Comparator must reject that
declaration before semantic acceptance.

This is a local algebraic identity, not a proof of the strict staple bound,
the #1041 short-path theorem, unrestricted Erdős #1041, Comparator
acceptance, Palomar qualification, novelty, or peer review.

On a supported Comparator host, run both configurations from
`formal_math/erdos257_period_noncollapse`:

```sh
systemd-run --property=RestrictAddressFamilies=~AF_UNIX --user --pty \
  -E PATH="$PATH" --working-directory "$PWD" -- \
  bash -c 'lake env comparator ExternalVerification1041StapleEquality/comparator.json'

systemd-run --property=RestrictAddressFamilies=~AF_UNIX --user --pty \
  -E PATH="$PATH" --working-directory "$PWD" -- \
  bash -c 'lake env comparator ExternalVerification1041StapleEquality/comparator-negative-mismatch.json'
```

The positive run should succeed; the negative run should reject the extra
argument.  These are replay recipes only.  A local Lean compile does not imply
Comparator acceptance or Palomar review, and this directory performs no
outbound action.
