# Erdős #1041: coefficient-controlled cyclic tetranomial spokes

For a quotient root of
`g(w) = w^m + a*w^r + b*w^s + c`, Abel summation rewrites the complete
root spoke as a subconvex combination of the constant, the middle tail, and
the leading root power. The package compares the exact factorization, the
sharp root-dependent condition `‖c‖ + ‖b‖ * ‖w‖^s < 1`, and the
coefficient-only corollary `‖b‖ + ‖c‖ ≤ 1`. The coefficient `a` is
unrestricted.

Lean proves these root-spoke statements under the exact weak exponent order
`1 ≤ s ≤ r ≤ m`. The ordinary analytic theorem for genuine tetranomials uses
`m > r > s ≥ 1`, selects two suitable quotient roots, lifts their spokes
through `f(z) = g((z-h)^q)`, and checks the broken-line length. Those
root-selection, cyclic-fibre, and path-assembly steps are not formalized here.
The coefficient-free unrestricted tetranomial selector and unrestricted
Erdős #1041 remain open.

The Challenge imports only Mathlib. Both Comparator configs enable NanoDa and
permit exactly `propext`, `Quot.sound`, and `Classical.choice`. This is a
first-wave Palomar candidate pending focused Lean/axiom checks,
supported-runner positive and negative replay, and an immutable public source
identity. It is not a novelty, peer-review, acceptance, or submission claim.

`lakefile.toml` registration is intentionally left to the integrating agent.

The guarded focused build is pending after exit `75`: 5,707,309,056 bytes
were free against the 17,179,869,184-byte firewall minimum. This is a capacity
receipt, not proof evidence; raw Lake bypass is forbidden.
