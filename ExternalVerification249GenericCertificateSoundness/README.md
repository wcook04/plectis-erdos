# ExternalVerification249GenericCertificateSoundness

Two compared declarations about a coefficient sequence `c : ℕ → ℕ` with
`c n ≤ n`, drawn from the long record for Erdős Problem 249.

## Statements

`generic_soundness` is the certificate half. A finite integer window of length
`L` compares the block of coefficients after `N + h` with the block after `N`
and records their discrepancy as `window c h N L`. When that discrepancy sits
in the central arc modulo `2 ^ L`, at distance more than `N + h + L + 2` from
both endpoints, the tail shift `T c (N + h) - T c N` is not an integer.

`generic_tail_period` is the converse-side period law. When the binary value of
`c` is the rational `p / (2 ^ e * m)` with `m` positive and `m ∣ 2 ^ h - 1`,
every tail shift of step `h` above the preperiod `e` is an integer.

## Mechanism

Soundness is a purely integral separation. The analytic content is a bound: the
scaled tail difference sits within `N + h + L + 2` of the integer window, and an
integer inside the central arc modulo `2 ^ L` cannot be that close to any
multiple of `2 ^ L`. The period law rewrites the tail as
`2 ^ N * S - block c 0 N`, clears the denominator `2 ^ e * m` against
`2 ^ N * (2 ^ h - 1)`, and reads off an integer difference.

## Boundary

Neither declaration supplies a certificate for any particular sequence. Taken
with `c = φ` they say what a proof of irrationality for `∑_{n ≥ 1} φ(n) / 2 ^ n`
must produce and what a rational value would force. Neither settles Erdős
Problem 249, which remains open.

## Source

Live declarations
`ErdosProblems.Erdos249.PaperCompleteR7.GenericCertificates.generic_soundness`
and `...generic_tail_period` in
`ErdosProblems/Erdos249/PaperCompleteR7/GenericCertificates.lean`. That module
elaborates rc=0 and every public declaration in it depends on exactly `propext`,
`Classical.choice`, `Quot.sound`.

`Solution.lean` needs the `.olean` of the source module, which the serialized
project build produces. `Challenge.lean` elaborates on its own with the two
intentional specification sorries.
