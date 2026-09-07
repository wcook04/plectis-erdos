# Erdős #1041: finite-family translation avoidance

This directory isolates the source-backed generic-position lemma used by the
#1041 perturbation route:

```text
Every finite injective family of complex values admits an arbitrarily small
common translation after which all values are nonzero and no two lie on the
same positive ray.
```

`Challenge.lean` states that literal result with only Mathlib imports.
`Solution.lean` proves the same name and type by transporting
`ErdosProblems.Erdos1041.exists_small_translation_separating_arguments` from
the source module.  The negative configuration adds an irrelevant `True`
hypothesis, producing a deliberate declaration-type mismatch for replay.

This is a finite-family translation-avoidance result.  It does not prove that
a polynomial perturbation preserves all required root geometry, establish a
critical-point path-length bound, or solve unrestricted Erdős #1041.  It is
also not a claim of Comparator acceptance, Palomar qualification, novelty, or
peer review.

On a supported Comparator host, run both configurations from
`formal_math/erdos257_period_noncollapse`:

```sh
systemd-run --property=RestrictAddressFamilies=~AF_UNIX --user --pty \
  -E PATH="$PATH" --working-directory "$PWD" -- \
  bash -c 'lake env comparator ExternalVerification1041TranslationAvoidance/comparator.json'

systemd-run --property=RestrictAddressFamilies=~AF_UNIX --user --pty \
  -E PATH="$PATH" --working-directory "$PWD" -- \
  bash -c 'lake env comparator ExternalVerification1041TranslationAvoidance/comparator-negative-mismatch.json'
```

The positive run should succeed.  The negative run should reject the
solution theorem because its declaration has the extra `hweak : True`
argument.  These commands are replay recipes only; a local Lean compile does
not imply Comparator acceptance or Palomar review, and this directory performs
no outbound action.
