# Erdős #249: the complete dyadic totient-kernel structure

This package isolates the strongest unconditional structural theorem currently
proved for the dyadic sections of Euler's totient.  For

\[
f_{j,r}(n)=\varphi(2^j n+r),\qquad 0\le r<2^j,
\]

retain the two zero-residue base channels and one channel for every odd
residue at every positive level.  The compared theorem proves simultaneously
that

- this odd-core family is linearly independent over `ℚ`;
- it spans the same subspace as every dyadic section `f_{j,r}`;
- the complete unreduced truncation through level `e` has exactly the same
  span as its duplicate-free canonical truncation; and
- the complete unreduced family through levels `0,...,e` has exact rank
  `2^e+1` for every `e ≥ 1`.

Thus the theorem identifies the complete linear-relation structure, not merely
an unbounded sequence of independent examples.  Even-residue channels account
for all repetitions.  The proof constructs CRT--Dirichlet separated minors:
one affine channel is made prime while each competing channel receives a fresh
prime divisor in a prescribed dyadic congruence class, yielding a
parity-separated evaluation matrix with nonzero determinant.

## Mathematical boundary

This is an unconditional theorem about `Nat.totient`, but it does not prove
irrationality of `∑ φ(n)/2^n`.  A rank route to Erdős #249 would additionally
need a converse showing that rationality of that series forces bounded dyadic
kernel rank.  No such compression theorem is claimed, and Erdős #249 remains
open.

`Challenge.lean` imports only Mathlib and reproduces the literal function and
index vocabulary.  `Solution.lean` transports the independent odd-core family,
the full-span equality, the exact finite canonical-span normal form, and the
resulting finite-truncation rank from the checked source module.  The
deliberate negative omits the finite normal form and rank conclusions, so
Comparator must reject it as an incomplete statement.

## Palomar disposition

This is a first-wave Palomar candidate.  An explicit basis theorem for all
dyadic sections of Euler's totient, together with exact ranks for every finite
truncation, is a coherent research-note result with a number-theory and formal-
mathematics audience.  The missing rationality-to-finite-rank bridge is the
honest open boundary, not a reason to withhold the structural theorem.

Submission still requires a public GitHub repository at a full immutable
commit SHA, this exact config path, terminal positive acceptance, deliberate
negative rejection, and source-current metadata.  These local files are not a
Palomar decision, registry entry, novelty ruling, or peer review.
