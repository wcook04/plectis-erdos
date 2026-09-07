# Erdős #1041: root retention under a strict perturbation margin

This directory isolates the source-backed root-retention lemma used by the
#1041 perturbation route:

```text
For a positive-degree monic split complex polynomial whose roots have norm at
most rho, if ((natDegree + 1) * epsilon)^(natDegree)^(-1) + rho < 1 and
||shift|| < epsilon, every root of f + C shift lies strictly inside the unit
disk.
```

`Challenge.lean` states that literal result with only Mathlib imports.
`Solution.lean` proves the same name and type by transporting
`ErdosProblems.Erdos1041.constant_perturbation_roots_in_unitDisk` from the
source module.  The negative configuration adds an irrelevant `True`
hypothesis, producing a deliberate declaration-type mismatch for replay.

This is a quantitative root-continuity boundary, not a proof of unrestricted
Erdős #1041, a lemniscate path-length bound, or a claim of Comparator or
Palomar acceptance.  The source research packet records the exact claim
ceiling and the standard continuity-of-roots context.

On a supported Comparator host, run both configurations from
`formal_math/erdos257_period_noncollapse`:

```sh
systemd-run --property=RestrictAddressFamilies=~AF_UNIX --user --pty \
  -E PATH="$PATH" --working-directory "$PWD" -- \
  bash -c 'lake env comparator ExternalVerification1041RootRetention/comparator.json'

systemd-run --property=RestrictAddressFamilies=~AF_UNIX --user --pty \
  -E PATH="$PATH" --working-directory "$PWD" -- \
  bash -c 'lake env comparator ExternalVerification1041RootRetention/comparator-negative-mismatch.json'
```

The positive run should succeed.  The negative run should reject the
solution theorem because its declaration has the extra `hweak : True`
argument.  These commands are replay recipes only; a local Lean compile does
not imply Comparator acceptance or Palomar review, and this directory performs
no outbound action.
