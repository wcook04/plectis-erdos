/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib

/-!
# Trusted challenge for the Erdős #68 companion-orbit rationality boundary

Three theorems are exposed.

The first is the generic shift boundary. For every real `x`, the number
`x + ∑_{n≥2} 1/n!` is rational exactly when the canonical factorial digits of
`x` are eventually `m - 2`, and exactly when `⌊m! x⌋ ≡ -2 (mod m)` eventually.

The second specialises the boundary to the Erdős #68 series
`S = ∑_{d≥2} 1/(d! - 1)` through the fixed companion constant
`C = ∑_{n≥2} 1/(n!(n! - 1))`, in both the rational and the irrational
direction.

The third evaluates the anchored unit-factorial series as `exp 1 - 2`, which
is the identity that makes `C` the companion of `S`.

Each equivalence is exact in both directions. The statements do not produce
cofinal misses of the exceptional residue, so they do not prove irrationality
of `S` and Erdős #68 remains open.
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

/-- The generic shift boundary at an arbitrary real base point.

The two conjuncts give the canonical-digit form and the floor-residue form of
the same equivalence. The statement holds for every real `x`, so it covers
every member of the shifted family whose companion constant is named. -/
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
