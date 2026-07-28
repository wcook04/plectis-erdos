import Erdos249257.BooleanMobiusSkippedCoreExactRow

/-!
# Critical capacity for a skipped Boolean--Möbius core

This module isolates the exact quotient test corresponding to the sharp
upper-window capacity at endpoint `2c - 2`.
-/

namespace Erdos249257

open scoped BigOperators

/-- At the skipped-core endpoint `2c - 2`, fitting the binary repair below
the critical `2^(c-2)` threshold is exactly the assertion that adjoining the
crossing rank `c` makes the integral quotient reach the half target.

The below-half hypothesis is used only to make the truncated natural suffix
an honest subtraction.  The separate crossing-above hypothesis from the
skipped-core construction is deliberately absent: this theorem identifies
the remaining quantitative socket rather than assuming it. -/
theorem localBinarySuffix_two_mul_sub_two_lt_criticalCapacity_iff
    {D : Finset ℕ} {c : ℕ}
    (hc : 4 ≤ c)
    (hD : ∀ d ∈ D, 2 ≤ d ∧ d < c)
    (hbelow : localMersennePrefixValue D < (1 / 2 : ℚ)) :
    localBinarySuffix D 1 (2 * c - 2) < 2 ^ (c - 2) ↔
      2 ^ ((2 * c - 2) - 1) ≤
        localPrefixQuotient (insert c D) (2 * c - 2) := by
  classical
  let M := 2 * c - 2
  have hM : 1 ≤ M := by
    dsimp [M]
    omega
  have hcNotD : c ∉ D := by
    intro hcD
    have := (hD c hcD).2
    omega
  have hinsert :
      localPrefixQuotient (insert c D) M =
        localMersenneQuotient M c + localPrefixQuotient D M := by
    unfold localPrefixQuotient
    rw [Finset.sum_insert hcNotD]
  have hcQuotient : localMersenneQuotient M c = 2 ^ (c - 2) := by
    simpa [M] using localMersenneQuotient_two_mul_sub_two_self hc
  have hDtwo : ∀ d ∈ D, 2 ≤ d := fun d hd ↦ (hD d hd).1
  have hscaled :=
    scaled_localMersennePrefixValue (D := D) (M := M) hDtwo
  have hpowPos : (0 : ℚ) < (2 : ℚ) ^ M := by positivity
  have hlt := mul_lt_mul_of_pos_left hbelow hpowPos
  rw [hscaled] at hlt
  have hFnonneg : 0 ≤ localFractionMass D M := by
    unfold localFractionMass
    exact Finset.sum_nonneg fun d hd ↦
      (localMersenneFraction_pos (M := M) (hDtwo d hd)).le
  have hhalf :
      (2 : ℚ) ^ M * (1 / 2 : ℚ) = (2 : ℚ) ^ (M - 1) := by
    calc
      (2 : ℚ) ^ M * (1 / 2 : ℚ) =
          2 ^ ((M - 1) + 1) * (1 / 2 : ℚ) := by congr 2 <;> omega
      _ = (2 : ℚ) ^ (M - 1) := by rw [pow_succ]; ring
  rw [hhalf] at hlt
  have hquotientLtCast :
      (localPrefixQuotient D M : ℚ) < (2 : ℚ) ^ (M - 1) := by
    linarith
  have hquotientLt :
      localPrefixQuotient D M < 2 ^ (M - 1) := by
    exact_mod_cast hquotientLtCast
  change
    localBinarySuffix D 1 M < 2 ^ (c - 2) ↔
      2 ^ (M - 1) ≤ localPrefixQuotient (insert c D) M
  rw [hinsert, hcQuotient]
  unfold localBinarySuffix
  omega

/-! ## The fractional-mass obstruction -/

/-- A scaled prefix which is already above one half must have reached the
integral half target as soon as its total fractional mass is at most one.

This is the general carry statement behind the skipped-core socket below:
failure of the integral carry can only happen when more than one full unit is
hidden in the sum of the individual Mersenne residues. -/
theorem halfTarget_le_localPrefixQuotient_of_value_above_fractionMass_le_one
    {E : Finset ℕ} {M : ℕ}
    (hM : 1 ≤ M)
    (hE : ∀ d ∈ E, 2 ≤ d)
    (habove : (1 / 2 : ℚ) < localMersennePrefixValue E)
    (hfrac : localFractionMass E M ≤ 1) :
    2 ^ (M - 1) ≤ localPrefixQuotient E M := by
  have hpowPos : (0 : ℚ) < (2 : ℚ) ^ M := by positivity
  have hscaledAbove := mul_lt_mul_of_pos_left habove hpowPos
  have hscaled := scaled_localMersennePrefixValue (D := E) (M := M) hE
  have hhalf :
      (2 : ℚ) ^ M * (1 / 2 : ℚ) = ((2 ^ (M - 1) : ℕ) : ℚ) := by
    calc
      (2 : ℚ) ^ M * (1 / 2 : ℚ) =
          2 ^ ((M - 1) + 1) * (1 / 2 : ℚ) := by
            congr 2 <;> omega
      _ = (2 : ℚ) ^ (M - 1) := by rw [pow_succ]; ring
      _ = ((2 ^ (M - 1) : ℕ) : ℚ) := by norm_num
  rw [hhalf, hscaled] at hscaledAbove
  by_contra hnot
  have hquotLt : localPrefixQuotient E M < 2 ^ (M - 1) :=
    Nat.lt_of_not_ge hnot
  have hsucc : localPrefixQuotient E M + 1 ≤ 2 ^ (M - 1) := by omega
  have hsuccCast :
      (localPrefixQuotient E M : ℚ) + 1 ≤ ((2 ^ (M - 1) : ℕ) : ℚ) := by
    exact_mod_cast hsucc
  linarith

/-- For a crossing skipped core, the sharp `c-2`-bit repair capacity follows
from the single residue estimate that the inserted support carries at most
one unit of total fractional mass at endpoint `2c-2`. -/
theorem localBinarySuffix_two_mul_sub_two_lt_criticalCapacity_of_insertFractionMass
    {D : Finset ℕ} {c : ℕ}
    (hc : 4 ≤ c)
    (hD : ∀ d ∈ D, 2 ≤ d ∧ d < c)
    (hbelow : localMersennePrefixValue D < (1 / 2 : ℚ))
    (hcross : (1 / 2 : ℚ) < localMersennePrefixValue (insert c D))
    (hfrac : localFractionMass (insert c D) (2 * c - 2) ≤ 1) :
    localBinarySuffix D 1 (2 * c - 2) < 2 ^ (c - 2) := by
  apply (localBinarySuffix_two_mul_sub_two_lt_criticalCapacity_iff
    hc hD hbelow).2
  apply halfTarget_le_localPrefixQuotient_of_value_above_fractionMass_le_one
    (M := 2 * c - 2) (by omega) ?_ hcross hfrac
  intro d hd
  rw [Finset.mem_insert] at hd
  rcases hd with rfl | hd
  · omega
  · exact (hD d hd).1

/-- The same sufficient condition split into the old core residue mass and
the newly inserted rank.  This isolates a useful analytic subcase; the
one-unit bound is not asserted for every crossing core. -/
theorem localBinarySuffix_two_mul_sub_two_lt_criticalCapacity_of_splitFractionMass
    {D : Finset ℕ} {c : ℕ}
    (hc : 4 ≤ c)
    (hD : ∀ d ∈ D, 2 ≤ d ∧ d < c)
    (hbelow : localMersennePrefixValue D < (1 / 2 : ℚ))
    (hcross : (1 / 2 : ℚ) < localMersennePrefixValue (insert c D))
    (hfrac : localFractionMass D (2 * c - 2) +
      localMersenneFraction (2 * c - 2) c ≤ 1) :
    localBinarySuffix D 1 (2 * c - 2) < 2 ^ (c - 2) := by
  classical
  have hcNotD : c ∉ D := by
    intro hcD
    have := (hD c hcD).2
    omega
  have hmass :
      localFractionMass (insert c D) (2 * c - 2) =
        localMersenneFraction (2 * c - 2) c +
          localFractionMass D (2 * c - 2) := by
    unfold localFractionMass
    rw [Finset.sum_insert hcNotD]
  apply localBinarySuffix_two_mul_sub_two_lt_criticalCapacity_of_insertFractionMass
    hc hD hbelow hcross
  rw [hmass]
  linarith

/-- Consequently, failure of the sharp capacity at an actual crossing forces
strictly more than one unit of fractional residue mass.  This records the
precise analytic obstruction without assuming that it can occur. -/
theorem one_lt_splitFractionMass_of_criticalCapacity_failure
    {D : Finset ℕ} {c : ℕ}
    (hc : 4 ≤ c)
    (hD : ∀ d ∈ D, 2 ≤ d ∧ d < c)
    (hbelow : localMersennePrefixValue D < (1 / 2 : ℚ))
    (hcross : (1 / 2 : ℚ) < localMersennePrefixValue (insert c D))
    (hfail : ¬ localBinarySuffix D 1 (2 * c - 2) < 2 ^ (c - 2)) :
    1 < localFractionMass D (2 * c - 2) +
      localMersenneFraction (2 * c - 2) c := by
  by_contra hnot
  have hle : localFractionMass D (2 * c - 2) +
      localMersenneFraction (2 * c - 2) c ≤ 1 := le_of_not_gt hnot
  exact hfail
    (localBinarySuffix_two_mul_sub_two_lt_criticalCapacity_of_splitFractionMass
      hc hD hbelow hcross hle)

/-- The one-unit fractional-mass hypothesis is sufficient, but not necessary.
At the genuine crossing `D = {2,3}`, `c = 5`, the combined residue mass is
already greater than one while the sharp critical capacity still holds. -/
theorem splitFractionMass_one_bound_not_necessary_fixture :
    localMersennePrefixValue ({2, 3} : Finset ℕ) < (1 / 2 : ℚ) ∧
    (1 / 2 : ℚ) <
      localMersennePrefixValue (insert 5 ({2, 3} : Finset ℕ)) ∧
    1 < localFractionMass ({2, 3} : Finset ℕ) 8 +
      localMersenneFraction 8 5 ∧
    localBinarySuffix ({2, 3} : Finset ℕ) 1 8 < 2 ^ 3 := by
  norm_num [localMersennePrefixValue, mersenneWeightRat,
    localFractionMass, localMersenneFraction, localBinarySuffix,
    localPrefixQuotient, localMersenneQuotient]

end Erdos249257
