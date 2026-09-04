# Erdős #68: companion-orbit rationality boundary

Write `S = ∑_{d≥2} 1/(d! − 1)` for the Erdős #68 series and
`C = ∑_{n≥2} 1/(n!(n! − 1))` for its fixed companion constant. For a real `x`
write `F_m(x) = ⌊m! x⌋` and `d_m(x) = F_m(x) − m F_{m−1}(x)` for the canonical
mixed-radix factorial digit.

This Mathlib-only challenge exposes three source-current statements.

`companionOrbitBoundary_genericShift` holds at every real base point `x`. The
number `x + (e − 2)` is rational exactly when there is an `M` with
`d_m(x) = m − 2` for every `m ≥ M`, and exactly when there is an `M` with
`F_m(x) ≡ −2 (mod m)` for every `m ≥ M`.

`companionOrbitBoundary_factorialGapSeries` specialises that boundary to the
literal series. `S` is rational exactly when `F_m(C) ≡ −2 (mod m)` for all
sufficiently large `m`, and `S` is irrational exactly when for every bound `B`
there is an `m > B` with `F_m(C) ≢ −2 (mod m)`.

`tsum_unitFactTerm_eq_exp_one_sub_two` evaluates the anchored unit-factorial
series as `∑_{n≥2} 1/n! = e − 2`. That evaluation is the shift under which `C`
is the companion of `S`, since `C + (e − 2) = S`.

The generic base point is what carries the shifted family `∑_{n≥2} 1/(n! + t)`.
Each member of that family differs from `e − 2` by an explicit constant, so the
first theorem decides its rationality from the factorial orbit of that constant
alone. The member `t = −1` is the one carried out in full here, through the
identity `C + (e − 2) = S`.

Every statement in the package is an exact equivalence in both directions. The
boundary is that an equivalence supplies no cofinal miss of the exceptional
residue by itself, so this package leaves the irrationality of `S` undecided
and Erdős #68 open.

`Challenge.lean` is Mathlib-only, NanoDa is enabled, and the axiom budget is
exactly `propext`, `Quot.sound`, and `Classical.choice`. The package is
registered in `lakefile.toml` as the lean_lib
`ExternalVerification68CompanionOrbitBoundary`.
