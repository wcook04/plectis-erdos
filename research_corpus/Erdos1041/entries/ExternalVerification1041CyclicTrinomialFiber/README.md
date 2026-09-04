# Erdős #1041: cyclic-trinomial fibre spokes

For the translated cyclic trinomial
`f(z) = (z-h)^(q*m) + a*(z-h)^(q*r) + c`, put `w = (z-h)^q`.
The package compares the exact quotient-root factorization, the theorem that
every radial quotient-root spoke stays strictly inside `|f| < 1` when
`‖w‖ < 1` and `‖c‖ < 1`, and the strict length budget for two selected fibre
displacements of norm below one.

These are the formal kernel of a structured positive family. They do not
formalize the ordinary finite root-selection argument, the choice of two
distinct members of one cyclic fibre, the lift of quotient spokes to those
members, or assembly of the broken line as a path in the relevant lemniscate
component. They do not solve unrestricted Erdős #1041.

The Challenge imports only Mathlib. Both Comparator configs enable NanoDa and
permit exactly `propext`, `Quot.sound`, and `Classical.choice`. This is a
first-wave Palomar candidate pending focused Lean/axiom checks, supported-runner
positive and negative replay, and an immutable public source identity. It is
not a novelty, peer-review, acceptance, or submission claim.

`lakefile.toml` registration is intentionally left to the integrating agent.

The guarded focused build is pending after exit `75`: 12,691,898,368 bytes
were free against the 17,179,869,184-byte firewall minimum. This is a capacity
receipt, not proof evidence; raw Lake bypass is forbidden.
