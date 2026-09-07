# Erdős #1041: signed-moment tetranomial selector

This package compares the strongest finite-family endpoint in
`ErdosProblems.Erdos1041.TetranomialL2Selector`. An exact polarization identity
retains the signed mixed moment
`2 Re(conj c * b * ∑ i in S, v i)`. Energy below `card S - 1` then forces two
distinct indexed strict unit tails. For an indexed finite family of roots of
`w^m + a*w^r + b*w^s + c`, the source theorem feeds those tails into the Abel
spoke decomposition and proves that both complete root spokes remain strictly
inside the unit lemniscate.

This strictly advances the coefficient-controlled package's pointwise spoke
interface: Lean now performs the two-index selection under the exact signed
moment budget. The hypotheses do not make the root map injective, so distinct
indices need not denote distinct root values. The theorem also does not derive
the moment budget from arbitrary
tetranomial coefficients, show that the supplied finite family is a complete
root multiset, lift through a translated cyclic power, construct a path
object, or solve unrestricted Erdős #1041.

`Challenge.lean` imports only Mathlib. The positive solution transports three
exact source declarations; the deliberate negative changes the strongest
interface by adding an extra argument. Both Comparator configs enable NanoDa
and permit exactly `propext`, `Quot.sound`, and `Classical.choice`.

`lakefile.toml` and the central Palomar portfolio are intentionally outside
this package's write scope. No external submission, acceptance, novelty, or
peer-review claim is made.

The guarded focused build was deferred with exit `75`: 1,364,934,656 bytes
were free against the 17,179,869,184-byte firewall minimum. This is a typed
capacity receipt, not proof evidence; raw Lake bypass and build retries are
forbidden until the stated storage floor is restored.
