# Erdős #1041: solved Newton identity

This directory isolates the finite algebraic step that solves the reversed
polynomial Newton identity for the reciprocal coordinate `p m`.  It exposes
the current coefficient and lower-coordinate terms explicitly, which is the
normalisation used by the reciprocal expansion.

`Challenge.lean` states the literal result with only Mathlib imports.
`Solution.lean` transports the same theorem from
`ErdosProblems.Erdos1041.ReciprocalNewtonExpansion`.  The negative fixture
adds an irrelevant `True` hypothesis, so Comparator must reject that
declaration before semantic acceptance.

This is a finite identity, not a proof of the reciprocal logarithmic series,
the #1041 short-path theorem, or unrestricted Erdős #1041.  It is also not a
claim of Comparator acceptance, Palomar qualification, novelty, or peer
review.

On a supported Comparator host, run both configurations from
`formal_math/erdos257_period_noncollapse`:

```sh
systemd-run --property=RestrictAddressFamilies=~AF_UNIX --user --pty \
  -E PATH="$PATH" --working-directory "$PWD" -- \
  bash -c 'lake env comparator ExternalVerification1041NewtonSolve/comparator.json'

systemd-run --property=RestrictAddressFamilies=~AF_UNIX --user --pty \
  -E PATH="$PATH" --working-directory "$PWD" -- \
  bash -c 'lake env comparator ExternalVerification1041NewtonSolve/comparator-negative-mismatch.json'
```

The positive run should succeed; the negative run should reject the extra
argument.  These are replay recipes only.  A local Lean compile does not imply
Comparator acceptance or Palomar review, and this directory performs no
outbound action.
