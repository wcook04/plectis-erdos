/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib

/-!
# Trusted challenge for the Möbius–Mersenne ladder structure in Erdős #249

Two signed Möbius series over the Mersenne denominators are separated here.
The **power ladder** is `Θᵣ = ∑_{d ≥ 1} μ(d) / (2^d - 1)^r`, with the exponent
`r` on the denominator.  The **literal Lambert ladder** is
`Θ̂ᵣ = ∑_{d ≥ 1} μ(d) / (2^(r·d) - 1)`, the plain Möbius–Lambert series
evaluated at `q = 2⁻ʳ`.

The compared family records that the power ladder satisfies no finite
constant-coefficient linear recurrence, that it is strictly log-concave at
every rung `r ≥ 1` with strictly negative order-two Hankel determinant, that
the literal Lambert ladder equals `2⁻ʳ` and has vanishing shifted Hankel
determinants in every order at least two, and that the two ladders disagree
on `r ≥ 1`.

No statement here concerns irrationality of the Erdős #249 constant, and no
statement here asserts a measure representation for either ladder.
-/

namespace Erdos249257.ExternalVerification249MobiusMersenneLadderStructure

open scoped BigOperators
open ArithmeticFunction

/-- The `n`th atom of the Möbius–Mersenne power ladder, with the positive
integer index shifted to `n + 1`. -/
noncomputable def mobiusMersenneTerm (r n : ℕ) : ℝ :=
  ((moebius (n + 1) : ℤ) : ℝ) /
    (((2 : ℝ) ^ (n + 1) - 1) ^ r)

/-- The Möbius–Mersenne power ladder `Θᵣ = ∑_{d ≥ 1} μ(d) / (2^d - 1)^r`. -/
noncomputable def mobiusMersenneTheta (r : ℕ) : ℝ :=
  ∑' n : ℕ, mobiusMersenneTerm r n

/-- The literal Möbius–Lambert rung `Θ̂ᵣ = ∑_{d ≥ 1} μ(d) / (2^(r·d) - 1)`. -/
noncomputable def mobiusMersenneLambertRung (r : ℕ) : ℝ :=
  ∑' d : ℕ+, ((moebius (d : ℕ) : ℤ) : ℝ) / ((2 : ℝ) ^ (r * (d : ℕ)) - 1)

/-- No finite constant-coefficient linear recurrence holds for the power ladder
even eventually. -/
theorem mobiusMersenneTheta_no_linearRecurrence_of_eventually
    {m : ℕ} (c : Fin (m + 1) → ℝ) (n₀ : ℕ) (hc : ∃ k, c k ≠ 0)
    (hrec : ∀ n : ℕ, n₀ ≤ n →
      ∑ k : Fin (m + 1), c k * mobiusMersenneTheta (n + (k : ℕ)) = 0) : False := by
  sorry

/-- The power ladder satisfies no finite constant-coefficient linear
recurrence on `n ≥ 1`. -/
theorem mobiusMersenneTheta_no_linearRecurrence :
    ¬ ∃ (m : ℕ) (c : Fin (m + 1) → ℝ), (∃ k, c k ≠ 0) ∧
        ∀ n : ℕ, 1 ≤ n →
          ∑ k : Fin (m + 1), c k * mobiusMersenneTheta (n + (k : ℕ)) = 0 := by
  sorry

/-- The power ladder is strictly log-concave at every rung `r ≥ 1`. -/
theorem mobiusMersenneTheta_strict_logConcave (r : ℕ) (hr : 1 ≤ r) :
    mobiusMersenneTheta r * mobiusMersenneTheta (r + 2) <
      mobiusMersenneTheta (r + 1) ^ 2 := by
  sorry

/-- The shifted order-two Hankel determinant of the power ladder is strictly
negative at every rung `r ≥ 1`. -/
theorem mobiusMersenneTheta_hankel_two_neg (r : ℕ) (hr : 1 ≤ r) :
    mobiusMersenneTheta r * mobiusMersenneTheta (r + 2) -
      mobiusMersenneTheta (r + 1) ^ 2 < 0 := by
  sorry

/-- The literal Lambert ladder collapses to `2⁻ʳ`. -/
theorem mobiusMersenneLambertRung_eq (r : ℕ) (hr : 1 ≤ r) :
    mobiusMersenneLambertRung r = ((1 : ℝ) / 2) ^ r := by
  sorry

/-- Every shifted Hankel determinant of the literal Lambert ladder of order at
least two vanishes. -/
theorem lambertRung_shifted_hankelDet_eq_zero (s N : ℕ) (hs : 1 ≤ s) (hN : 2 ≤ N) :
    Matrix.det (Matrix.of fun i j : Fin N =>
      mobiusMersenneLambertRung (s + (i : ℕ) + (j : ℕ))) = 0 := by
  sorry

/-- The two ladders disagree somewhere on `r ≥ 1`. -/
theorem mobiusMersenneTheta_ne_mobiusMersenneLambertRung :
    ¬ ∀ r : ℕ, 1 ≤ r → mobiusMersenneTheta r = mobiusMersenneLambertRung r := by
  sorry

end Erdos249257.ExternalVerification249MobiusMersenneLadderStructure
