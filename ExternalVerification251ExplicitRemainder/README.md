# ExternalVerification251ExplicitRemainder

## Statement

With `g`, `T`, the shift `T (N + h) - T N` and the finite signed window `S` as
in the prime-gap dyadic series, and

    P x = x ^ 4 + 8 x ^ 3 + 36 x ^ 2 + 104 x + 150,
    E = 1250 / 2 ^ L * (P (N + h + L + 2) + P (N + L + 2)),

`explicit_remainder_certificate` proves three things at once: the window
approximates the shift with error at most `E`; a window satisfying
`|S| + E < 1` keeps the shift inside the open unit interval; and a window
satisfying `E < dist(S, ℤ)` makes the shift non-integral.

## Mechanism

The gaps obey the elementary polynomial bound `g n ≤ 1250 (n + 2) ^ 4`, and the
weighted quartic telescopes exactly, so the complete tail after index `N` is at
most `1250 P (N + 2)`. The omitted part of the shift after the length-`L`
window is the later complete shift scaled by `2 ^ (-L)`, so the two tail bounds
give the displayed constant with nothing left unevaluated.

## Boundary

The bound is unconditional. It exhibits no block satisfying either
certificate, and it does not settle Erdős Problem #251, which remains open.

## Provenance

Transported from `ErdosProblems/Erdos251/PaperTailBoundsR7.lean` in the private
`formal_math/erdos257_period_noncollapse` project. Toolchain
`leanprover/lean4:v4.29.1`, Mathlib `5e932f97dd25535344f80f9dd8da3aab83df0fe6`.
