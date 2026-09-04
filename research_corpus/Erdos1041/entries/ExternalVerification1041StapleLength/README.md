# Erdős #1041: staple-length strict bound

This directory isolates the geometric inequality showing that the equal-radius
staple joining two roots in the open unit disk has length strictly below two.
The bound spends no polynomial-dependent margin: it follows from the two root
moduli and the nonnegative segment parameter alone.

`Challenge.lean` states the literal result with only Mathlib imports.
`Solution.lean` transports the same theorem from
`ErdosProblems.Erdos1041.ReciprocalNewtonExpansion`.  The negative fixture
adds an irrelevant `True` hypothesis, so Comparator must reject that
declaration before semantic acceptance.

This is a local geometric bound, not a proof of the #1041 short-path theorem,
the reciprocal logarithmic series, unrestricted Erdős #1041, Comparator
acceptance, Palomar qualification, novelty, or peer review.

On a supported Comparator host, run both configurations from
`formal_math/erdos257_period_noncollapse`:

```sh
systemd-run --property=RestrictAddressFamilies=~AF_UNIX --user --pty \
  -E PATH="$PATH" --working-directory "$PWD" -- \
  bash -c 'lake env comparator ExternalVerification1041StapleLength/comparator.json'

systemd-run --property=RestrictAddressFamilies=~AF_UNIX --user --pty \
  -E PATH="$PATH" --working-directory "$PWD" -- \
  bash -c 'lake env comparator ExternalVerification1041StapleLength/comparator-negative-mismatch.json'
```

The positive run should succeed; the negative run should reject the extra
argument.  These are replay recipes only.  A local Lean compile does not imply
Comparator acceptance or Palomar review, and this directory performs no
outbound action.
