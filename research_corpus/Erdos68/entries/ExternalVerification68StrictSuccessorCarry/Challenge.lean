/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib

/-!
# Trusted challenge for the Erdős #68 companion-orbit and strict-successor characterizations

The first theorem gives a fixed-constant factorial-orbit characterization:
the series is rational exactly when `⌊m! C⌋ ≡ -2 (mod m)` eventually, and it
is irrational exactly when this residue is missed cofinally.  The second
theorem gives a lossless integer strict-successor reformulation.  At every
index `m ≥ 3`, a unit carry is equivalent to the computable divisibility test

`m ∣ strictFacTopRat (factorialGapPrefix m) m`.

The theorem therefore identifies the exact missing producer without claiming
that the producer has been proved.  It does not prove irrationality of the
series or solve Erdős #68.
-/

namespace Erdos249257.ExternalVerification68StrictSuccessorCarry

noncomputable section

/-- The literal factorial-gap series from Erdős #68. -/
noncomputable def factorialGapSeries : ℝ :=
  ∑' d : ℕ, if 1 < d then
    (1 : ℝ) / ((((d.factorial : ℤ) - 1 : ℤ) : ℝ))
  else 0

/-- The fixed companion constant
`C = ∑_{n≥2} 1/(n!(n!-1))`. -/
noncomputable def companionConstant : ℝ :=
  ∑' n : ℕ, if 2 ≤ n then
    (1 : ℝ) /
      ((n.factorial : ℝ) * ((((n.factorial : ℤ) - 1 : ℤ) : ℝ)))
  else 0

/-- Floor of the factorially scaled companion orbit. -/
noncomputable def facFloor (x : ℝ) (m : ℕ) : ℤ :=
  ⌊(m.factorial : ℝ) * x⌋

/-- The exact rational prefix through index `n`. -/
def factorialGapPrefix (n : ℕ) : ℚ :=
  ∑ k ∈ Finset.Icc 2 n, 1 / ((k.factorial : ℚ) - 1)

/-- The first integer strictly above the factorially scaled real prefix. -/
noncomputable def strictFacTop (x : ℝ) (n : ℕ) : ℤ :=
  ⌊(n.factorial : ℝ) * x⌋ + 1

/-- Exact rational implementation of the same strict successor. -/
def strictFacTopRat (x : ℚ) (n : ℕ) : ℤ :=
  ⌊(n.factorial : ℚ) * x⌋ + 1

/-- Distance from the preceding scaled prefix to its strict successor. -/
noncomputable def factorialGapPredecessorGap (m : ℕ) : ℝ :=
  (strictFacTop
      ((factorialGapPrefix (m - 1) : ℚ) : ℝ) (m - 1) : ℝ) -
    ((m - 1).factorial : ℝ) *
      ((factorialGapPrefix (m - 1) : ℚ) : ℝ)

/-- Exact integer carry in the strict-successor recurrence. -/
noncomputable def factorialGapStepCarry (m : ℕ) : ℤ :=
  -⌊1 + 1 / ((m.factorial : ℝ) - 1) -
      (m : ℝ) * factorialGapPredecessorGap m⌋

/-- Complete fixed-companion-orbit characterization.

The two conjuncts state the exact eventual exceptional-residue criterion for
rationality and its cofinal-miss dual for irrationality. -/
theorem companionOrbit_completeCharacterization :
    (¬Irrational factorialGapSeries ↔
      ∃ M : ℕ, ∀ m : ℕ, M ≤ m →
        ((facFloor companionConstant m + 2 : ℤ) % (m : ℤ)) = 0) ∧
    (Irrational factorialGapSeries ↔
      ∀ B : ℕ, ∃ m : ℕ, B < m ∧
        ((facFloor companionConstant m + 2 : ℤ) % (m : ℤ)) ≠ 0) := by
  sorry

/-- Complete carry and exact-prefix divisibility characterization.

The four conjuncts record respectively the rationality criterion, its
irrational cofinal dual, the pointwise carry/divisibility equivalence, and the
resulting purely integral cofinal reformulation. -/
theorem strictSuccessorCarry_completeCharacterization :
    (¬Irrational factorialGapSeries ↔
      ∃ M : ℕ, ∀ m : ℕ, M ≤ m → factorialGapStepCarry m = 1) ∧
    (Irrational factorialGapSeries ↔
      ∀ B : ℕ, ∃ m : ℕ, B < m ∧ factorialGapStepCarry m ≠ 1) ∧
    (∀ m : ℕ, 3 ≤ m →
      (factorialGapStepCarry m = 1 ↔
        (m : ℤ) ∣ strictFacTopRat (factorialGapPrefix m) m)) ∧
    (Irrational factorialGapSeries ↔
      ∀ B : ℕ, ∃ m : ℕ, B < m ∧
        ¬((m : ℤ) ∣ strictFacTopRat (factorialGapPrefix m) m)) := by
  sorry


end

end Erdos249257.ExternalVerification68StrictSuccessorCarry
