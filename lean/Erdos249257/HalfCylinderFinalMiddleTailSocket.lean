import Erdos249257.HalfCylinderFinalMiddleCellEscape

/-!
# Quantitative tail sockets for the surviving final-middle cells

The large final-cell module owns the exact lazy-support carry translation.
This compact downstream surface turns that identity into the strict tail
bounds needed by later arithmetic sieves.  Keeping the projection separate
prevents a small analytic consequence from re-elaborating the entire
last-producer development and makes the `-2`/`-1` consumers visible at their
actual quantitative thresholds.
-/

namespace Erdos249257

open Set Filter
open HalfCarryReachability
open scoped BigOperators

noncomputable section

/-- Strict support deficit leaves strict room between the future coefficient
tail and the current integer carry. -/
theorem binaryCoeffTail_lt_integerHalfCarry_of_supportSeries_lt_half
    (A : Set ℕ) (hone : 1 ∉ A)
    (hseries : erdosSupportSeries 2 A < (1 : ℝ) / 2)
    (N : ℕ) :
    binaryCoeffTail (supportCoeff A) (N + 1) <
      (integerHalfCarry A N : ℝ) := by
  have hid := integerHalfCarry_eq_scaled_residual_add_tail A hone N
  have hscaled :
      0 < (2 : ℝ) ^ (N + 1) *
        ((1 : ℝ) / 2 - erdosSupportSeries 2 A) := by
    exact mul_pos (by positivity) (sub_pos.mpr hseries)
  rw [hid]
  exact lt_add_of_pos_left _ hscaled

/-- Below one half, the lazy future tail fits strictly below the finite
producer charge plus four. -/
theorem binaryCoeffTail_union_Ioi_lt_producerCarry_add_four
    (U : Set ℕ) (D : ℕ) (hD3 : 3 ≤ D)
    (hU : U ⊆ Set.Iio D)
    (hone : 1 ∉ U ∪ Set.Ioi D)
    (hseries : erdosSupportSeries 2 (U ∪ Set.Ioi D) < (1 : ℝ) / 2) :
    binaryCoeffTail (supportCoeff (U ∪ Set.Ioi D)) (2 * D + 2) <
      ((producerCarry (insert D U) D + 4 : ℤ) : ℝ) := by
  have htail :=
    binaryCoeffTail_lt_integerHalfCarry_of_supportSeries_lt_half
      (U ∪ Set.Ioi D) hone hseries (2 * D + 1)
  rw [integerHalfCarry_union_Ioi_eq_producerCarry_add_four
    U D hD3 hU] at htail
  simpa only [show 2 * D + 1 + 1 = 2 * D + 2 by omega] using htail

/-- A final producer cell `-2` forces the lazy future coefficient tail below
two. -/
theorem binaryCoeffTail_union_Ioi_lt_two_of_producerCarry_eq_neg_two
    (U : Set ℕ) (D : ℕ) (hD3 : 3 ≤ D)
    (hU : U ⊆ Set.Iio D)
    (hone : 1 ∉ U ∪ Set.Ioi D)
    (hseries : erdosSupportSeries 2 (U ∪ Set.Ioi D) < (1 : ℝ) / 2)
    (hcell : producerCarry (insert D U) D = -2) :
    binaryCoeffTail (supportCoeff (U ∪ Set.Ioi D)) (2 * D + 2) < 2 := by
  have htail := binaryCoeffTail_union_Ioi_lt_producerCarry_add_four
    U D hD3 hU hone hseries
  have hcharge :
      ((producerCarry (insert D U) D + 4 : ℤ) : ℝ) = 2 := by
    rw [hcell]
    norm_num
  rw [hcharge] at htail
  exact htail

/-- A final producer cell `-1` forces the lazy future coefficient tail below
three. -/
theorem binaryCoeffTail_union_Ioi_lt_three_of_producerCarry_eq_neg_one
    (U : Set ℕ) (D : ℕ) (hD3 : 3 ≤ D)
    (hU : U ⊆ Set.Iio D)
    (hone : 1 ∉ U ∪ Set.Ioi D)
    (hseries : erdosSupportSeries 2 (U ∪ Set.Ioi D) < (1 : ℝ) / 2)
    (hcell : producerCarry (insert D U) D = -1) :
    binaryCoeffTail (supportCoeff (U ∪ Set.Ioi D)) (2 * D + 2) < 3 := by
  have htail := binaryCoeffTail_union_Ioi_lt_producerCarry_add_four
    U D hD3 hU hone hseries
  have hcharge :
      ((producerCarry (insert D U) D + 4 : ℤ) : ℝ) = 3 := by
    rw [hcell]
    norm_num
  rw [hcharge] at htail
  exact htail

#print axioms binaryCoeffTail_lt_integerHalfCarry_of_supportSeries_lt_half
#print axioms binaryCoeffTail_union_Ioi_lt_producerCarry_add_four
#print axioms binaryCoeffTail_union_Ioi_lt_two_of_producerCarry_eq_neg_two
#print axioms binaryCoeffTail_union_Ioi_lt_three_of_producerCarry_eq_neg_one

end

end Erdos249257
