# Erdős #1041: Orlicz non-uniform linear lower-bound obstruction

This directory isolates the source theorem that a transform sublinear at
zero cannot dominate positive age by one positive universal linear constant.
It is the logical obstruction behind the no-uniform-linear-boundary result.

`Challenge.lean` states the literal result with only Mathlib imports.
`Solution.lean` transports the same theorem from
`ErdosProblems.Erdos1041.AttachmentAgeLifetimeOrlicz`.  The negative fixture
adds an irrelevant `True` hypothesis, so Comparator must reject that
declaration before semantic acceptance.

This is a local ordered-logic result, not a proof of the full #1041
short-path theorem, unrestricted Erdős #1041, Comparator acceptance, Palomar
qualification, novelty, or peer review.

On a supported Comparator host, run both configurations from
`formal_math/erdos257_period_noncollapse`:

```sh
systemd-run --property=RestrictAddressFamilies=~AF_UNIX --user --pty \
  -E PATH="$PATH" --working-directory "$PWD" -- \
  bash -c 'lake env comparator ExternalVerification1041OrliczNoUniformLinear/comparator.json'

systemd-run --property=RestrictAddressFamilies=~AF_UNIX --user --pty \
  -E PATH="$PATH" --working-directory "$PWD" -- \
  bash -c 'lake env comparator ExternalVerification1041OrliczNoUniformLinear/comparator-negative-mismatch.json'
```

The positive run should succeed; the negative run should reject the extra
argument.  These are replay recipes only.  A local Lean compile does not
imply Comparator acceptance or Palomar review, and this directory performs
no outbound action.
