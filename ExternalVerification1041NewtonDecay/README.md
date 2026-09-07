# Erdős #1041: the Newton-decay ray obstruction

This directory isolates the source-backed endpoint obstruction used by the
#1041 Newton-flow route:

```text
If two endpoint values are not on the same positive ray, they cannot satisfy
the exact relation endValue = exp(-time) * startValue.
```

`Challenge.lean` states that literal result with only Mathlib imports.
`Solution.lean` proves the same name and type by transporting
`ErdosProblems.Erdos1041.no_newtonConnection_of_not_samePositiveRay` from the
source module.  The negative configuration adds an irrelevant `True`
hypothesis, producing a deliberate declaration-type mismatch for replay.

This is an endpoint obstruction supplied by exponential value decay.  It does
not establish that a short connecting curve exists, prove a path-length bound,
or solve unrestricted Erdős #1041.  It is also not a claim of Comparator
acceptance, Palomar qualification, novelty, or peer review.

On a supported Comparator host, run both configurations from
`formal_math/erdos257_period_noncollapse`:

```sh
systemd-run --property=RestrictAddressFamilies=~AF_UNIX --user --pty \
  -E PATH="$PATH" --working-directory "$PWD" -- \
  bash -c 'lake env comparator ExternalVerification1041NewtonDecay/comparator.json'

systemd-run --property=RestrictAddressFamilies=~AF_UNIX --user --pty \
  -E PATH="$PATH" --working-directory "$PWD" -- \
  bash -c 'lake env comparator ExternalVerification1041NewtonDecay/comparator-negative-mismatch.json'
```

The positive run should succeed.  The negative run should reject the
solution theorem because its declaration has the extra `hweak : True`
argument.  These commands are replay recipes only; a local Lean compile does
not imply Comparator acceptance or Palomar review, and this directory performs
no outbound action.
