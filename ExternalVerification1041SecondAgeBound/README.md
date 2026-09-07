# Erdős #1041: second-age tail bound

This directory isolates the ordered-age step that turns
`(count - 1) * secondAge ≤ total` into the sharp threshold
`secondAge ≤ total / (count - 1)`.

`Challenge.lean` states the literal result with only Mathlib imports.
`Solution.lean` transports the same theorem from
`ErdosProblems.Erdos1041.AttachmentAgeLifetimeOrlicz`.  The negative fixture
adds an irrelevant `True` hypothesis, so Comparator must reject that
declaration before semantic acceptance.

This is a local ordered-algebra result, not a proof of the full #1041
short-path theorem, unrestricted Erdős #1041, Comparator acceptance, Palomar
qualification, novelty, or peer review.

On a supported Comparator host, run both configurations from
`formal_math/erdos257_period_noncollapse`:

```sh
systemd-run --property=RestrictAddressFamilies=~AF_UNIX --user --pty \
  -E PATH="$PATH" --working-directory "$PWD" -- \
  bash -c 'lake env comparator ExternalVerification1041SecondAgeBound/comparator.json'

systemd-run --property=RestrictAddressFamilies=~AF_UNIX --user --pty \
  -E PATH="$PATH" --working-directory "$PWD" -- \
  bash -c 'lake env comparator ExternalVerification1041SecondAgeBound/comparator-negative-mismatch.json'
```

The positive run should succeed; the negative run should reject the extra
argument.  These are replay recipes only.  A local Lean compile does not
imply Comparator acceptance or Palomar review, and this directory performs
no outbound action.
