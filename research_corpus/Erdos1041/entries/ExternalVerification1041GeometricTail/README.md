# Erdős #1041: geometric tail identity

This directory isolates the convergent geometric-series identity used to sum
the reciprocal Newton expansion's coefficient tails.  For a nonnegative ratio
`q < 1`, the tail beginning at `N + 1` is exactly
`q^(N+1)/(1-q)`.

`Challenge.lean` states the literal result with only Mathlib imports.
`Solution.lean` transports the same theorem from
`ErdosProblems.Erdos1041.ReciprocalNewtonExpansion`.  The negative fixture
adds an irrelevant `True` hypothesis, so Comparator must reject that
declaration before semantic acceptance.

This is a summation helper, not a proof of the full reciprocal expansion,
the #1041 short-path theorem, or unrestricted Erdős #1041.  It is also not a
claim of Comparator acceptance, Palomar qualification, novelty, or peer
review.

On a supported Comparator host, run both configurations from
`formal_math/erdos257_period_noncollapse`:

```sh
systemd-run --property=RestrictAddressFamilies=~AF_UNIX --user --pty \
  -E PATH="$PATH" --working-directory "$PWD" -- \
  bash -c 'lake env comparator ExternalVerification1041GeometricTail/comparator.json'

systemd-run --property=RestrictAddressFamilies=~AF_UNIX --user --pty \
  -E PATH="$PATH" --working-directory "$PWD" -- \
  bash -c 'lake env comparator ExternalVerification1041GeometricTail/comparator-negative-mismatch.json'
```

The positive run should succeed; the negative run should reject the extra
argument.  These are replay recipes only.  A local Lean compile does not imply
Comparator acceptance or Palomar review, and this directory performs no
outbound action.
