/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib

/-!
# Trusted challenge for the Erdős #68 companion-orbit rationality boundary

Four theorems are exposed.

The first is the strict-successor carry boundary for the Erdős #68 series
`S = ∑_{d≥2} 1/(d! - 1)`. Write `H_m` for the exact rational prefix of `S`
through index `m` and `Z_m = ⌊m! H_m⌋ + 1` for the first integer strictly
above the factorially scaled prefix. The theorem states that `S` is rational
exactly when the recurrence carry is eventually one, that `S` is irrational
exactly when the carry is cofinally different from one, that at every index
`m ≥ 3` a unit carry is equivalent to the divisibility `m ∣ Z_m`, and that
`S` is irrational exactly when `m ∤ Z_m` holds cofinally. The last conjunct
is a purely integral form of the irrationality question over exact rational
prefixes.

The second is the generic shift boundary. For every real `x`, the number
`x + ∑_{n≥2} 1/n!` is rational exactly when the canonical factorial digits of
`x` are eventually `m - 2`, and exactly when `⌊m! x⌋ ≡ -2 (mod m)` eventually.

The third specialises the boundary to `S` through the fixed companion constant
`C = ∑_{n≥2} 1/(n!(n! - 1))`, in both the rational and the irrational
direction.

The fourth evaluates the anchored unit-factorial series as `exp 1 - 2`, which
is the identity that makes `C` the companion of `S`.

Each equivalence is exact in both directions. The statements do not produce
cofinal misses of the exceptional residue or cofinal divisibility failures, so
they do not prove irrationality of `S` and Erdős #68 remains open.
-/

namespace Erdos249257.ExternalVerification68CompanionOrbitBoundary

noncomputable section

/-- The literal factorial-gap series from Erdős #68. -/
noncomputable def factorialGapSeries : ℝ :=
  ∑' d : ℕ, if 1 < d then
    (1 : ℝ) / ((((d.factorial : ℤ) - 1 : ℤ) : ℝ))
  else 0

/-- The fixed companion constant `C = ∑_{n≥2} 1/(n!(n! - 1))`. -/
noncomputable def companionConstant : ℝ :=
  ∑' n : ℕ, if 2 ≤ n then
    (1 : ℝ) /
      ((n.factorial : ℝ) * ((((n.factorial : ℤ) - 1 : ℤ) : ℝ)))
  else 0

/-- The anchored unit-factorial term `1/n!`, supported on `n ≥ 2`. -/
noncomputable def unitFactTerm (n : ℕ) : ℝ :=
  if 2 ≤ n then (1 : ℝ) / ((n.factorial : ℝ)) else 0

/-- Floor of the factorially scaled real number. -/
noncomputable def facFloor (x : ℝ) (m : ℕ) : ℤ :=
  ⌊(m.factorial : ℝ) * x⌋

/-- The canonical mixed-radix factorial digit at radix `m`. -/
noncomputable def canonicalDigit (x : ℝ) (m : ℕ) : ℤ :=
  facFloor x m - (m : ℤ) * facFloor x (m - 1)

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

/-- The strict-successor carry boundary for the Erdős #68 series.

The four conjuncts record respectively the rationality criterion in terms of
eventual unit carries, its cofinal dual for irrationality, the pointwise
carry and divisibility equivalence at every index `m ≥ 3`, and the resulting
purely integral cofinal reformulation over the exact rational prefixes. -/
theorem companionOrbitBoundary_strictSuccessorCarry :
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

/-- The generic shift boundary at an arbitrary real base point.

The two conjuncts give the canonical-digit form and the floor-residue form of
the same equivalence. The statement holds for every real `x`. Specialisation
to a named member of the shifted family uses the identity relating that member
to its companion constant, which is outside this entry. -/
theorem companionOrbitBoundary_genericShift (x : ℝ) :
    (¬Irrational (x + ∑' n : ℕ, unitFactTerm n) ↔
      ∃ M : ℕ, ∀ m : ℕ, M ≤ m → canonicalDigit x m = (m : ℤ) - 2) ∧
    (¬Irrational (x + ∑' n : ℕ, unitFactTerm n) ↔
      ∃ M : ℕ, ∀ m : ℕ, M ≤ m →
        ((facFloor x m + 2 : ℤ) % (m : ℤ)) = 0) := by
  sorry

/-- The Erdős #68 companion-orbit boundary.

The first conjunct is the rationality criterion for the literal series. The
second is its cofinal-miss dual for irrationality. -/
theorem companionOrbitBoundary_factorialGapSeries :
    (¬Irrational factorialGapSeries ↔
      ∃ M : ℕ, ∀ m : ℕ, M ≤ m →
        ((facFloor companionConstant m + 2 : ℤ) % (m : ℤ)) = 0) ∧
    (Irrational factorialGapSeries ↔
      ∀ B : ℕ, ∃ m : ℕ, B < m ∧
        ((facFloor companionConstant m + 2 : ℤ) % (m : ℤ)) ≠ 0) := by
  sorry

/-- The anchored unit-factorial series is exactly `exp 1 - 2`. -/
theorem tsum_unitFactTerm_eq_exp_one_sub_two :
    (∑' n : ℕ, unitFactTerm n) = Real.exp 1 - 2 := by
  sorry

end

end Erdos249257.ExternalVerification68CompanionOrbitBoundary
