# Erdős #249: full-depth ray amplifier

This package captures the source-current theorem that the certificate-depth
lock is free. One finite certificate on a ray forces depth-equals-period
certificates in every adjacent pair of sufficiently large multipliers, hence
an eventually two-syndetic set. Pointwise, such a full-depth certificate
exists exactly when the seed tail difference is nonintegral. Consequently
`ApFullDepthEscape`, the cofinal full-depth supply, and the older arbitrary-
depth period-multiple supply are each exactly equivalent to Erdős #249.

This strictly supersedes the older description of full-depth escape as merely
sufficient. It does not produce the first seed on any ray, so irrationality
remains open.

The Challenge is Mathlib-only; both configs enable NanoDa and permit exactly
`propext`, `Quot.sound`, and `Classical.choice`. First-wave Palomar candidate;
no novelty, external review, acceptance, or submission is claimed.

`lakefile.toml` registration remains for the integrating agent.

Focused Lean replay was attempted through the guarded build on 2026-08-31 and
was deferred before compilation at the repository low-disk firewall:
5,747,892,224 bytes free versus the 17,179,869,184-byte minimum. Static
package checks remain available; Lean validity and the axiom audit are pending
until that storage re-entry condition is met.
