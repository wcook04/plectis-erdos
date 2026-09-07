# Erdős #68: adjacent-unit-carry window

This Mathlib-only challenge exposes four source-current statements: the exact
positive-offset criterion for two consecutive unit carries, the two-step
denominator telescope, the resulting window-denominator identity, and the
unconditional mixed-radix offset factorization.  The latter retains the full
weighted two-carry defect; specializing both carries to one makes the defect
vanish and shows that the proposed post-assumption prime-power obstruction is
only the universal reduced-fraction bound in another coordinate.

The family is an exact no-go theorem for that strategy, not an irrationality
proof. Erdős #68 remains open. The package is a first-wave Palomar candidate;
external positive and deliberate-negative replay and an immutable public SHA
remain pending. `Challenge.lean` is Mathlib-only, NanoDa is enabled, and the
axiom budget is exactly `propext`, `Quot.sound`, and `Classical.choice`.

The package is intentionally not registered in `lakefile.toml`; registration
is a separate residual owned by the integrating agent.

The guarded focused build is pending after exit `75`: 11,122,528,256 bytes
were free against the 17,179,869,184-byte firewall minimum. This is a capacity
receipt, not proof evidence; raw Lake bypass is forbidden.
