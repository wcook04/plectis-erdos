# Erdős #243: summable normalized-negative-mass rigidity

This package isolates a complete conditional rigidity theorem for an exact
product-cleared reciprocal-tail orbit.  Write

\[
D_{n+1}=a_nD_n,\qquad C_{n+1}=a_nC_n-D_n,
\]

and let the centered state be

\[
E_n=D_n-(a_n-1)C_n.
\]

Assume `Cₙ > 0`, the exact identity `Cₙ₊₁ = Cₙ - Eₙ`, division-free
normalized vanishing (`K|Eₙ| < Cₙ` eventually for every fixed `K`), and
summability of

\[
\frac{|\min(E_n,0)|}{C_n}.
\]

The compared theorem proves both:

- `Eₙ = 0` eventually; and
- `aₙ₊₁ = aₙ² - aₙ + 1` eventually.

This is a whole-orbit conditional result, with no periodicity hypothesis.  It
is a distinct branch from bounded raw negative error: summability controls the
normalized total negative mass rather than imposing an eventual pointwise
lower bound on `Eₙ`.

## Mathematical boundary

The theorem does not establish its summability or normalized-vanishing
hypotheses for every reciprocal-tail orbit.  It therefore does not settle
unrestricted Erdős #243.  The open parent problem is an explicit theorem
boundary, not a reason to omit the conditional rigidity result.

`Challenge.lean` imports only Mathlib and exposes the exact two-conclusion
endpoint.  `Solution.lean` transports the source-current theorems
`eventually_zero_of_summable_negativeRelativeMass` and
`sylvesterNext_eventually_of_summable_negativeRelativeMass`.  The deliberate
negative adds an irrelevant hypothesis, so Comparator must reject its changed
theorem type.

## Verification

From `formal_math/erdos257_period_noncollapse`:

```sh
./scripts/lean_fast_build.py --jobs 2 \
  ExternalVerification243SummableNegativeMassRigidity/Challenge.lean \
  ExternalVerification243SummableNegativeMassRigidity/Solution.lean \
  ExternalVerification243SummableNegativeMassRigidity/NegativeSolution.lean \
  ExternalVerification243SummableNegativeMassRigidity/AxiomAudit.lean
```

The Comparator configs enable both the Lean kernel and NanoDa and permit only
`propext`, `Quot.sound`, and `Classical.choice`.  Terminal positive acceptance
and deliberate-negative rejection require a supported runner; no local file
is represented as that external verdict.

The focused local build is currently pending: the guarded build firewall
returned exit `75` because 13,669,040,128 bytes were free against its
17,179,869,184-byte minimum.  This is an environment-capacity receipt, not
proof evidence.  Re-run the exact command above after storage clearance.

## Palomar disposition

This is a first-wave Palomar candidate: it is a coherent exact theorem family,
not merely a subordinate periodic no-go.  Submission still requires a public
repository at an immutable full commit SHA, supported-runner positive and
negative replay receipts, and source-current metadata.  This package makes no
novelty, registry, editorial, or peer-review claim.
