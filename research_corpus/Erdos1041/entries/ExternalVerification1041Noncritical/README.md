# Erdős #1041: a quantitative noncriticality margin

This directory isolates the source-backed perturbative lemma used on a
protected region of the #1041 route:

```text
If the derivative has norm at least `lower` on a set, a perturbation of norm
strictly less than `lower` cannot create a zero of the perturbed derivative
there.
```

`Challenge.lean` states that literal result with only Mathlib imports.
`Solution.lean` proves the same name and type by transporting
`ErdosProblems.Erdos1041.noncritical_on_of_norm_lt_uniform_lower_bound` from
the source module.  The negative configuration adds an irrelevant `True`
hypothesis, producing a deliberate declaration-type mismatch for replay.

This is a local uniform-margin lemma.  It does not prove that a suitable
margin exists globally, establish a critical-point path-length bound, or
solve unrestricted Erdős #1041.  It is also not a claim of Comparator
acceptance, Palomar qualification, novelty, or peer review.

On a supported Comparator host, run both configurations from
`formal_math/erdos257_period_noncollapse`:

```sh
systemd-run --property=RestrictAddressFamilies=~AF_UNIX --user --pty \
  -E PATH="$PATH" --working-directory "$PWD" -- \
  bash -c 'lake env comparator ExternalVerification1041Noncritical/comparator.json'

systemd-run --property=RestrictAddressFamilies=~AF_UNIX --user --pty \
  -E PATH="$PATH" --working-directory "$PWD" -- \
  bash -c 'lake env comparator ExternalVerification1041Noncritical/comparator-negative-mismatch.json'
```

The positive run should succeed.  The negative run should reject the
solution theorem because its declaration has the extra `hweak : True`
argument.  These commands are replay recipes only; a local Lean compile does
not imply Comparator acceptance or Palomar review, and this directory
performs no outbound action.
