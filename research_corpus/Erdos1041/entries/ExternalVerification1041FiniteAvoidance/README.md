# Erdős #1041: finite affine-line avoidance

This directory isolates the finite geometric kernel used to choose a small
constant translation that avoids all forbidden real affine lines.  In the
Newton-flow route, those lines encode zero critical values and positive-ray
collisions; the level-separation extension adds perpendicular bisectors.

`Challenge.lean` states the literal result using `Set.range` only.
`Solution.lean` transports the same theorem from
`ErdosProblems.Erdos1041.NewtonFlowRaySeparation`.  The negative fixture adds
an irrelevant `True` hypothesis, so Comparator must reject that declaration
before semantic acceptance.

This is a finite-avoidance lemma, not a proof of the #1041 short-path theorem,
a path-length bound, or unrestricted Erdős #1041.  It is also not a claim of
Comparator acceptance, Palomar qualification, novelty, or peer review.

On a supported Comparator host, run both configurations from
`formal_math/erdos257_period_noncollapse`:

```sh
systemd-run --property=RestrictAddressFamilies=~AF_UNIX --user --pty \
  -E PATH="$PATH" --working-directory "$PWD" -- \
  bash -c 'lake env comparator ExternalVerification1041FiniteAvoidance/comparator.json'

systemd-run --property=RestrictAddressFamilies=~AF_UNIX --user --pty \
  -E PATH="$PATH" --working-directory "$PWD" -- \
  bash -c 'lake env comparator ExternalVerification1041FiniteAvoidance/comparator-negative-mismatch.json'
```

The positive run should succeed; the negative run should reject the extra
argument.  These are replay recipes only.  A local Lean compile does not
imply Comparator acceptance or Palomar review, and this directory performs
no outbound action.
