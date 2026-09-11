import Erdos249257.BooleanMobiusCarry
import Erdos249257.GreedyAchievementSet

/-!
# Producer carry and complete future-tail socket

This module isolates the exact one-sided condition found by the fixed-tail
audit: a middle producer's landing carry only has to beat its complete future
divisor-incidence tail.  A sufficiently negative upper-producer carry is
automatically on the opposite side of `1/2`, with an explicit Mersenne-gap
margin.
-/

namespace Erdos249257

open Set Filter
open scoped BigOperators

/-- The producer-aligned affine integer carry. -/
noncomputable def producerCarry (A : Set ℕ) (d : ℕ) : ℤ :=
  affineBinaryOrbit
    (fun n : ℕ ↦ (supportCoeff A (n + 1) : ℤ)) 1 (2 * d + 1)

/-- The finite-prefix carry identity at the producer-aligned depth `2d+1`.
The support hypothesis matches an adjacent-above producer prefix, whose
ranks are all at most `d`. -/
theorem producerCarry_residual_identity
    (A : Set ℕ) (d : ℕ)
    (hone : 1 ∉ A)
    (hA : A ⊆ Set.Iic d) :
    (1 : ℝ) / 2 - erdosSupportSeries 2 A =
      ((producerCarry A d : ℝ) -
          binaryCoeffTail (supportCoeff A) (2 * d + 2)) /
        (2 : ℝ) ^ (2 * d + 2) := by
  have hsubset : A ⊆ Set.Iic (2 * d + 2) := by
    intro a ha
    exact Set.mem_Iic.mpr ((Set.mem_Iic.mp (hA ha)).trans (by omega))
  have hinter : A ∩ Set.Iic (2 * d + 2) = A :=
    Set.inter_eq_left.mpr hsubset
  have h := halfFinitePrefix_residual_eq_pow_mul_integerCarry_sub_finiteTail
    A hone (2 * d + 1)
  rw [show 2 * d + 1 + 1 = 2 * d + 2 by omega, hinter] at h
  simpa [producerCarry] using h

/-- Exact middle-producer safety criterion: the adjacent-above prefix is
below `1/2` iff its positive integer landing carry beats the complete future
divisor-incidence tail. -/
theorem producerCarry_gt_tail_iff_supportSeries_lt_half
    (A : Set ℕ) (d : ℕ)
    (hone : 1 ∉ A)
    (hA : A ⊆ Set.Iic d) :
    binaryCoeffTail (supportCoeff A) (2 * d + 2) <
        (producerCarry A d : ℝ) ↔
      erdosSupportSeries 2 A < (1 : ℝ) / 2 := by
  have hid := producerCarry_residual_identity A d hone hA
  have hden : (0 : ℝ) < (2 : ℝ) ^ (2 * d + 2) := by positivity
  constructor
  · intro hcarry
    have hnum : (0 : ℝ) <
        (producerCarry A d : ℝ) -
          binaryCoeffTail (supportCoeff A) (2 * d + 2) :=
      sub_pos.mpr hcarry
    have hres : (0 : ℝ) < (1 : ℝ) / 2 - erdosSupportSeries 2 A := by
      rw [hid]
      exact div_pos hnum hden
    linarith
  · intro hseries
    have hres : (0 : ℝ) < (1 : ℝ) / 2 - erdosSupportSeries 2 A := by
      linarith
    rw [hid] at hres
    have hnum : (0 : ℝ) <
        (producerCarry A d : ℝ) -
          binaryCoeffTail (supportCoeff A) (2 * d + 2) :=
      (div_pos_iff_of_pos_right hden).mp hres
    exact sub_pos.mp hnum

/-- The complementary exact upper-producer criterion. -/
theorem producerCarry_lt_tail_iff_half_lt_supportSeries
    (A : Set ℕ) (d : ℕ)
    (hone : 1 ∉ A)
    (hA : A ⊆ Set.Iic d) :
    (producerCarry A d : ℝ) <
        binaryCoeffTail (supportCoeff A) (2 * d + 2) ↔
      (1 : ℝ) / 2 < erdosSupportSeries 2 A := by
  have hid := producerCarry_residual_identity A d hone hA
  have hden : (0 : ℝ) < (2 : ℝ) ^ (2 * d + 2) := by positivity
  constructor
  · intro hcarry
    have hnum :
        (producerCarry A d : ℝ) -
            binaryCoeffTail (supportCoeff A) (2 * d + 2) < 0 :=
      sub_neg.mpr hcarry
    have hres : (1 : ℝ) / 2 - erdosSupportSeries 2 A < 0 := by
      rw [hid]
      exact div_neg_of_neg_of_pos hnum hden
    linarith
  · intro hseries
    have hres : (1 : ℝ) / 2 - erdosSupportSeries 2 A < 0 := by
      linarith
    rw [hid] at hres
    have hnum :
        (producerCarry A d : ℝ) -
            binaryCoeffTail (supportCoeff A) (2 * d + 2) < 0 :=
      by simpa using (div_lt_iff₀ hden).mp hres
    exact sub_neg.mp hnum

/-- The support-coefficient strip gives a theorem-ready square-root
sufficient condition for middle-producer safety. -/
theorem producerCarry_sqrt_sufficient
    (A : Set ℕ) (d : ℕ)
    (hone : 1 ∉ A)
    (hA : A ⊆ Set.Iic d)
    (hcarry :
      2 * Real.sqrt ((2 * d + 2 : ℕ) : ℝ) + 4 <
        (producerCarry A d : ℝ)) :
    erdosSupportSeries 2 A < (1 : ℝ) / 2 := by
  have htail := binaryCoeffTail_supportCoeff_le_two_sqrt_add_four
    A (2 * d + 2)
  apply (producerCarry_gt_tail_iff_supportSeries_lt_half A d hone hA).mp
  exact htail.trans_lt hcarry

/-- Elementary fallback: for `d ≥ 1`, the affine bound `2d+6` dominates
the square-root tail strip. -/
theorem producerCarry_linear_sufficient
    (A : Set ℕ) (d : ℕ)
    (hone : 1 ∉ A)
    (hA : A ⊆ Set.Iic d)
    (hd : 1 ≤ d)
    (hcarry :
      2 * (d : ℝ) + 6 < (producerCarry A d : ℝ)) :
    erdosSupportSeries 2 A < (1 : ℝ) / 2 := by
  have hdR : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hsqrt :
      Real.sqrt (((2 * d + 2 : ℕ) : ℝ)) ≤ (d : ℝ) + 1 := by
    rw [Real.sqrt_le_iff]
    constructor
    · positivity
    · push_cast
      nlinarith
  apply producerCarry_sqrt_sufficient A d hone hA
  nlinarith

/-- A negative upper-producer integer carry is automatically strictly below
the nonnegative incidence tail. -/
theorem producerCarry_neg_forces_half_lt_supportSeries
    (A : Set ℕ) (d : ℕ)
    (hone : 1 ∉ A)
    (hA : A ⊆ Set.Iic d)
    (hcarry : producerCarry A d < 0) :
    (1 : ℝ) / 2 < erdosSupportSeries 2 A := by
  apply (producerCarry_lt_tail_iff_half_lt_supportSeries A d hone hA).mp
  have htail := binaryCoeffTail_nonneg (supportCoeff A) (2 * d + 2)
  have hcarryR :
      (producerCarry A d : ℝ) < 0 := by
    exact_mod_cast hcarry
  exact hcarryR.trans_le htail

/-- Eight units at depth `2d+1` dominate the entire rank-`d`
superincreasing gap. -/
theorem mersenneGap_lt_eight_div_four_pow_succ
    (d : ℕ) (hd : 2 ≤ d) :
    mersenneGap d < (8 : ℝ) / (4 : ℝ) ^ (d + 1) := by
  have hgap := four_pow_mul_next_mersenneGap_le (d - 1)
  rw [show d - 1 + 1 = d by omega] at hgap
  have hpowHalf : ((1 : ℝ) / 2) ^ (d - 1) ≤ (1 : ℝ) / 2 := by
    exact pow_le_of_le_one (by norm_num) (by norm_num) (by omega)
  have hscaled :
      (4 : ℝ) ^ (d - 1) * mersenneGap d < (1 : ℝ) / 2 := by
    calc
      (4 : ℝ) ^ (d - 1) * mersenneGap d
          ≤ (1 / 6 : ℝ) + (3 / 8 : ℝ) * ((1 : ℝ) / 2) ^ (d - 1) := hgap
      _ ≤ (1 / 6 : ℝ) + (3 / 8 : ℝ) * ((1 : ℝ) / 2) := by
        gcongr
      _ < (1 : ℝ) / 2 := by norm_num
  have hpow : (0 : ℝ) < (4 : ℝ) ^ (d - 1) := by positivity
  have hdiv : mersenneGap d <
      ((1 : ℝ) / 2) / (4 : ℝ) ^ (d - 1) := by
    exact (lt_div_iff₀ hpow).2 (by simpa [mul_comm] using hscaled)
  have heq :
      ((1 : ℝ) / 2) / (4 : ℝ) ^ (d - 1) =
        (8 : ℝ) / (4 : ℝ) ^ (d + 1) := by
    rw [show d + 1 = (d - 1) + 2 by omega, pow_add]
    norm_num
    field_simp
    norm_num
  rwa [heq] at hdiv

/-- An upper-producer carry of at most `-8` puts the adjacent-above prefix
more than one full Mersenne gap above `1/2`. -/
theorem producerCarry_le_neg_eight_forces_gap_margin
    (A : Set ℕ) (d : ℕ)
    (hone : 1 ∉ A)
    (hA : A ⊆ Set.Iic d)
    (hd : 2 ≤ d)
    (hcarry : producerCarry A d ≤ -8) :
    (1 : ℝ) / 2 + mersenneGap d < erdosSupportSeries 2 A := by
  have hid := producerCarry_residual_identity A d hone hA
  have htail := binaryCoeffTail_nonneg (supportCoeff A) (2 * d + 2)
  have hcarryR : (producerCarry A d : ℝ) ≤ -8 := by
    exact_mod_cast hcarry
  have hnum : (8 : ℝ) ≤
      binaryCoeffTail (supportCoeff A) (2 * d + 2) -
        (producerCarry A d : ℝ) := by
    linarith
  have hpowEq :
      (2 : ℝ) ^ (2 * d + 2) = (4 : ℝ) ^ (d + 1) := by
    rw [show 2 * d + 2 = 2 * (d + 1) by omega, pow_mul]
    norm_num
  have hexcess :
      erdosSupportSeries 2 A - (1 : ℝ) / 2 =
        (binaryCoeffTail (supportCoeff A) (2 * d + 2) -
          (producerCarry A d : ℝ)) / (4 : ℝ) ^ (d + 1) := by
    calc
      erdosSupportSeries 2 A - (1 : ℝ) / 2 =
          -((1 : ℝ) / 2 - erdosSupportSeries 2 A) := by ring
      _ = -(((producerCarry A d : ℝ) -
            binaryCoeffTail (supportCoeff A) (2 * d + 2)) /
          (2 : ℝ) ^ (2 * d + 2)) := by rw [hid]
      _ = (binaryCoeffTail (supportCoeff A) (2 * d + 2) -
            (producerCarry A d : ℝ)) / (4 : ℝ) ^ (d + 1) := by
        rw [hpowEq]
        ring
  have hden : (0 : ℝ) < (4 : ℝ) ^ (d + 1) := by positivity
  have hlower : (8 : ℝ) / (4 : ℝ) ^ (d + 1) ≤
      erdosSupportSeries 2 A - (1 : ℝ) / 2 := by
    rw [hexcess]
    exact div_le_div_of_nonneg_right hnum hden.le
  have hgap := mersenneGap_lt_eight_div_four_pow_succ d hd
  linarith

/-- If the adjacent-above prefix is `base + w_d`, the preceding margin says
that replacing `w_d` by the entire later tail still remains above `1/2`.
This is the analytic forced-return statement for the upper producer. -/
theorem producerCarry_le_neg_eight_forces_belowTail_gt_half
    (A : Set ℕ) (d : ℕ) (base : ℝ)
    (hone : 1 ∉ A)
    (hA : A ⊆ Set.Iic d)
    (hd : 2 ≤ d)
    (hcarry : producerCarry A d ≤ -8)
    (hdecomp : erdosSupportSeries 2 A = base + mersenneWeight d) :
    (1 : ℝ) / 2 < base + mersenneTail d := by
  have hmargin := producerCarry_le_neg_eight_forces_gap_margin
    A d hone hA hd hcarry
  rw [hdecomp] at hmargin
  unfold mersenneGap at hmargin
  linarith

#print axioms producerCarry_residual_identity
#print axioms producerCarry_gt_tail_iff_supportSeries_lt_half
#print axioms producerCarry_lt_tail_iff_half_lt_supportSeries
#print axioms producerCarry_sqrt_sufficient
#print axioms producerCarry_linear_sufficient
#print axioms producerCarry_neg_forces_half_lt_supportSeries
#print axioms mersenneGap_lt_eight_div_four_pow_succ
#print axioms producerCarry_le_neg_eight_forces_gap_margin
#print axioms producerCarry_le_neg_eight_forces_belowTail_gt_half

end Erdos249257
