# Erdős #1041: reciprocal boundary rigidity

This directory isolates the equality case in the supported-half-plane
argument.  If every nonzero displacement has nonnegative real part and the
reciprocal sum balances to zero, every displacement must lie on the
supporting line.

`Challenge.lean` states the literal result with only Mathlib imports.
`Solution.lean` transports the same theorem from
`ErdosProblems.Erdos1041.NewtonFlowRaySeparation`.  The negative fixture adds
an irrelevant `True` hypothesis, so Comparator must reject that declaration
before semantic acceptance.

This is a boundary-rigidity lemma, not a proof of the #1041 short-path
theorem, convex-hull decomposition, or unrestricted Erdős #1041.  It is also
not a claim of Comparator acceptance, Palomar qualification, novelty, or peer
review.

On a supported Comparator host, run both configurations from
`formal_math/erdos257_period_noncollapse`:

```sh
systemd-run --property=RestrictAddressFamilies=~AF_UNIX --user --pty \
  -E PATH="$PATH" --working-directory "$PWD" -- \
  bash -c 'lake env comparator ExternalVerification1041ReciprocalRigidity/comparator.json'

systemd-run --property=RestrictAddressFamilies=~AF_UNIX --user --pty \
  -E PATH="$PATH" --working-directory "$PWD" -- \
  bash -c 'lake env comparator ExternalVerification1041ReciprocalRigidity/comparator-negative-mismatch.json'
```

The positive run should succeed; the negative run should reject the extra
argument.  These are replay recipes only.  A local Lean compile does not
imply Comparator acceptance or Palomar review, and this directory performs
no outbound action.
