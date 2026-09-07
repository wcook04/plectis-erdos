# Erdős #249: canonical Mersenne arithmetic frontier

This package exposes the source-current arithmetic normal form of Erdős #249.
For a prospective denominator `2^c v`, with `v` positive and odd, it fixes the
block basepoint at `N = c`, chooses only an Euler-multiple height `H`, and asks
whether the explicit residue of the finite totient block modulo
`(2^H-1)/v` misses both endpoint intervals. Lean proves that this canonical
basepoint supply is exactly equivalent to irrationality of the binary totient
series. It also proves the finite residue recurrence and that the canonical
supply dominates the older remote-basepoint centered supply.

This is an exact equivalent reduction, not a proof of the still-open supply.
It dominates the remote-basepoint formulation by removing its `N` search; it
does not imply the distinct actual-LCM witness family instance by instance.

The Challenge is Mathlib-only; both configs enable NanoDa and permit exactly
`propext`, `Quot.sound`, and `Classical.choice`. This is a first-wave Palomar
candidate, not a novelty, peer-review, acceptance, or submission claim.

`lakefile.toml` registration remains for the integrating agent.

Focused Lean replay was attempted through the guarded build on 2026-08-31 and
was deferred before compilation at the repository low-disk firewall:
5,747,892,224 bytes free versus the 17,179,869,184-byte minimum. Static
package checks remain available; Lean validity and the axiom audit are pending
until that storage re-entry condition is met.
