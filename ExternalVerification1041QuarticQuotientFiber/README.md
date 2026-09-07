# Erdős #1041: translated quartic quotient fibres

Let `P` be a monic quartic and consider the translated cyclic lift
`f(z) = P((z-h)^q)` with `q ≥ 2`. Pendyala's degree-four theorem supplies the
quartic chord-or-radial geometric input. The new source-current family proves
the metric kernel that makes a quotient chord usable after taking a
`q`-th-root lift: the pointwise density bound, its exact integral, the strict
two-endpoint budget, and the final path-length fan-in.

The Challenge compares those four exact Lean declarations. It does not
formalize Pendyala's four-point radial lemma, the continuous covering-space
construction of a root lift (including a chord through zero), the ordinary
case split and path assembly, or the unrestricted Erdős #1041 problem. Those
are explicit proof/open boundaries, not hidden axioms.

The Challenge imports only Mathlib. Both Comparator configs enable NanoDa and
permit exactly `propext`, `Quot.sound`, and `Classical.choice`. This is a
first-wave Palomar candidate pending focused Lean/axiom checks,
supported-runner positive and negative replay, and an immutable public source
identity. It is not a novelty, peer-review, acceptance, or submission claim.

`lakefile.toml` registration is intentionally left to the integrating agent.

The guarded focused build is pending after exit `75`: 9,421,103,104 bytes
were free against the 17,179,869,184-byte firewall minimum. This is a capacity
receipt, not proof evidence; raw Lake bypass is forbidden.
