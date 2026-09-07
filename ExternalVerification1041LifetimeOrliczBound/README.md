# Erdős #1041: lifetime-to-Orlicz bound

This directory isolates the edge transform that converts an exact lifetime
factorization `lifetime = size * phi` and a positive size into the upper bound
`phi ≤ budget / size`.

`Challenge.lean` states the literal result with only Mathlib imports.
`Solution.lean` transports the same theorem from
`ErdosProblems.Erdos1041.AttachmentAgeLifetimeOrlicz`.  The negative fixture
adds an irrelevant `True` hypothesis, so Comparator must reject that
declaration before semantic acceptance.

This is a local ordered-algebra result, not a proof of the full #1041
short-path theorem, unrestricted Erdős #1041, Comparator acceptance, Palomar
qualification, novelty, or peer review.

## Palomar disposition: submit the coherent family

The attachment-age/lifetime Orlicz family is a Palomar candidate for the
operator-directed submission campaign.  Its research content is the exact
nonlinear transform `I_k(r) = k * Phi((1/k) * log (1/r))`, the sharp failure
of every positive uniform linear replacement, the weighted-chain Jensen
bounds, and the root-summed two-young-root selector.  The fact that Erdős
#1041 remains open is a theorem boundary, not an editorial veto.

This one division lemma should not be inflated into a standalone submission,
and the five existing scalar packages should not become five microsubmissions.
They are the formal consumer layer of one serious result family.  This
directory is the lead local disposition surface until a composite package
captures the analytic core at matching strength.  Submission readiness has
three exact remaining gates:

1. formalise or otherwise build the Palomar/Comparator interface for the
   integral substitution, convexity/Jensen argument, and merge-tree
   double-counting theorem rather than claiming that the present scalar
   declaration covers them;
2. record terminal positive replay and deliberate-negative rejection for the
   selected exact package on a supported runner; and
3. pin the selected project in the operator's submission repository at one
   immutable public commit.

Those are concrete completion gates, not a reason to suppress the theorem
from the paper or to abandon its Palomar submission disposition.

On a supported Comparator host, run both configurations from
`formal_math/erdos257_period_noncollapse`:

```sh
systemd-run --property=RestrictAddressFamilies=~AF_UNIX --user --pty \
  -E PATH="$PATH" --working-directory "$PWD" -- \
  bash -c 'lake env comparator ExternalVerification1041LifetimeOrliczBound/comparator.json'

systemd-run --property=RestrictAddressFamilies=~AF_UNIX --user --pty \
  -E PATH="$PATH" --working-directory "$PWD" -- \
  bash -c 'lake env comparator ExternalVerification1041LifetimeOrliczBound/comparator-negative-mismatch.json'
```

The positive run should succeed; the negative run should reject the extra
argument.  These are replay recipes only.  A local Lean compile does not
imply Comparator acceptance or Palomar review, and this directory performs
no outbound action.
